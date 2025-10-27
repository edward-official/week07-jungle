/*
 * mm-explicit.c - Explicit free list malloc package (doubly linked)
 *
 * Design (32-bit hdr/ftr, 8-byte alignment):
 * - Block layout (allocated):
 *   [ hdr | payload ... | ftr ]
 *
 * - Block layout (free, explicit list):
 *   [ hdr | pred ptr (8B) | succ ptr (8B) | ... | ftr ]
 *   We store two pointers in the payload for the doubly linked free list.
 *
 * - Header/Footer: 4 bytes each
 *   low bit: alloc (1 = allocated, 0 = free)
 *   remaining bits: block size (multiple of 8)
 *
 * Policies:
 * - First-fit search over an explicit doubly linked free list
 * - LIFO insertion at the head of the free list
 * - Coalesce on free and when extending the heap
 * - Split blocks when the remainder is at least the minimum block size
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * Team info
 ********************************************************/
team_t team = {
    "Krafton Jungle 11",          /* Team name */
    "Jongyun Lee",                /* First member's full name */
    "openmoresome@gmail.com",     /* First member's email address */
    "",                           /* Second member's full name (leave blank if none) */
    "",                           /* Second member's email address (leave blank if none) */
};

/* Alignment / size helpers */
#define ALIGNMENT 8
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE     4             /* word size (hdr/ftr) */
#define DSIZE     8             /* double word size */
#define CHUNKSIZE (1 << 12)     /* extend heap by this amount */
#define MAX(x,y)  ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)     ((char *)(bp) - WSIZE)
#define FTRP(bp)     ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks (by address) */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* ---- Explicit free list pointers stored in free block payload ----
 * We store two pointers (pred, succ) at the beginning of the free block payload.
 * Use 8-byte pointers (typical on 64-bit) and keep overall block 8-byte aligned.
 */
#define PRED_PTR(bp) ((char **)(bp))                    /* address to store pred pointer */
#define SUCC_PTR(bp) ((char **)((char *)(bp) + DSIZE))  /* address to store succ pointer */

#define GET_PRED(bp) (*(char **)(PRED_PTR(bp)))
#define GET_SUCC(bp) (*(char **)(SUCC_PTR(bp)))
#define SET_PRED(bp, ptr) (GET_PRED(bp) = (char *)(ptr))
#define SET_SUCC(bp, ptr) (GET_SUCC(bp) = (char *)(ptr))

/* Globals */
static char *heap_listp = NULL;   /* prologue payload pointer (like before) */
static char *free_listp = NULL;   /* head of the explicit free list */

/* Internal helpers (prototypes) */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void  place(void *bp, size_t asize);
static void  insert_node(void *bp);
static void  remove_node(void *bp);

/* Minimum free block size:
 * header(4) + footer(4) + pred ptr(8) + succ ptr(8) = 24 bytes -> aligned to 8 already
 */
#define MIN_FREE_BLK (ALIGN(WSIZE + WSIZE + DSIZE + DSIZE))  /* = 24 */

int mm_init(void)
{
    /* Create the initial empty heap: prologue hdr/ftr + epilogue */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);                            /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2 * WSIZE);

    free_listp = NULL;                             /* empty explicit list */

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));              /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));              /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));      /* New epilogue header */

    /* Coalesce with previous if free, and insert into free list */
    return coalesce(bp);
}

/* Insert a free block at the head of the free list (LIFO) */
static void insert_node(void *bp)
{
    SET_PRED(bp, NULL);
    SET_SUCC(bp, free_listp);
    if (free_listp != NULL)
        SET_PRED(free_listp, bp);
    free_listp = bp;
}

/* Remove a block from the free list */
static void remove_node(void *bp)
{
    char *pred = GET_PRED(bp);
    char *succ = GET_SUCC(bp);

    if (pred != NULL)
        SET_SUCC(pred, succ);
    else
        free_listp = succ;

    if (succ != NULL)
        SET_PRED(succ, pred);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    /* If neighbors are free, remove them from the list before merging */
    if (!prev_alloc) {
        remove_node(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    if (!next_alloc) {
        remove_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    /* Insert the coalesced block into the free list */
    insert_node(bp);
    return bp;
}

void *mm_malloc(size_t size)
{
    size_t asize;       /* Adjusted block size */
    size_t extendsize;  /* Amount to extend heap if no fit */
    char *bp;

    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs.
     * Alloc block needs at least header+footer (8B). For free blocks we need more,
     * but asize here is for allocated payload; splitting logic will ensure
     * remainder is >= MIN_FREE_BLK before creating a free block.
     */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    if (asize < MIN_FREE_BLK)
        asize = MIN_FREE_BLK;

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

void mm_free(void *bp)
{
    if (bp == NULL) return;

    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    /* Initialize free-list pointers in payload (optional but tidy) */
    SET_PRED(bp, NULL);
    SET_SUCC(bp, NULL);

    coalesce(bp);
}

void *mm_realloc(void *bp, size_t size)
{
    if (bp == NULL) return mm_malloc(size);
    if (size == 0) {
        mm_free(bp);
        return NULL;
    }

    size_t oldsize = GET_SIZE(HDRP(bp));
    size_t asize;
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    if (asize < MIN_FREE_BLK)
        asize = MIN_FREE_BLK;

    /* If the current block is already large enough, optionally split */
    if (asize <= oldsize) {
        size_t remain = oldsize - asize;
        if (remain >= MIN_FREE_BLK) {
            PUT(HDRP(bp), PACK(asize, 1));
            PUT(FTRP(bp), PACK(asize, 1));
            void *nbp = NEXT_BLKP(bp);
            PUT(HDRP(nbp), PACK(remain, 0));
            PUT(FTRP(nbp), PACK(remain, 0));
            SET_PRED(nbp, NULL);
            SET_SUCC(nbp, NULL);
            coalesce(nbp);
        }
        return bp;
    }

    /* Try to expand into next block if it is free and enough */
    void *next = NEXT_BLKP(bp);
    if (!GET_ALLOC(HDRP(next))) {
        size_t capacity = oldsize + GET_SIZE(HDRP(next));
        if (capacity >= asize) {
            /* Remove the next free block from list (we consume it) */
            remove_node(next);

            size_t remain = capacity - asize;
            PUT(HDRP(bp), PACK(capacity, 1));
            PUT(FTRP(bp), PACK(capacity, 1));

            if (remain >= MIN_FREE_BLK) {
                /* Shrink current to asize and create a new free remainder */
                PUT(HDRP(bp), PACK(asize, 1));
                PUT(FTRP(bp), PACK(asize, 1));
                void *nbp = NEXT_BLKP(bp);
                PUT(HDRP(nbp), PACK(remain, 0));
                PUT(FTRP(nbp), PACK(remain, 0));
                SET_PRED(nbp, NULL);
                SET_SUCC(nbp, NULL);
                insert_node(nbp);
            }
            return bp;
        }
    }

    /* Otherwise, malloc a new block, copy, free old */
    void *newbp = mm_malloc(size);
    if (newbp == NULL) return NULL;

    size_t copySize = oldsize - DSIZE; /* payload = block size - hdr(4) - ftr(4) */
    if (size < copySize) copySize = size;
    memcpy(newbp, bp, copySize);
    mm_free(bp);
    return newbp;
}

static void *find_fit(size_t asize)
{
    /* Best-fit on the explicit free list (linear scan) */
    char *best = NULL;
    size_t best_size = (size_t)(-1);

    for (char *bp = free_listp; bp != NULL; bp = GET_SUCC(bp)) {
        size_t csize = GET_SIZE(HDRP(bp));
        if (csize >= asize) {
            /* exact match면 바로 반환: 분할 오버헤드 최소화 */
            if (csize == asize)
                return bp;
            if (csize < best_size) {
                best = bp;
                best_size = csize;
            }
        }
    }
    return best; /* 없으면 NULL */
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    remove_node(bp); /* we are allocating this free block */

    if (csize - asize >= MIN_FREE_BLK) {
        /* Split: allocate front (bp) and free the remainder (nbp) */
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        void *nbp = NEXT_BLKP(bp);
        size_t rsize = csize - asize;
        PUT(HDRP(nbp), PACK(rsize, 0));
        PUT(FTRP(nbp), PACK(rsize, 0));
        SET_PRED(nbp, NULL);
        SET_SUCC(nbp, NULL);
        insert_node(nbp);
    } else {
        /* No split */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
