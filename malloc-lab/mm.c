/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    "Krafton Jungle 11", /* Team name */
    "Jongyun Lee", /* First member's full name */
    "openmoresome@gmail.com", /* First member's email address */
    "", /* Second member's full name (leave blank if none) */
    "", /* Second member's email address (leave blank if none) */
};

#define ALIGNMENT 8 /* single word (4) or double word (8) alignment */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7) /* rounds up to the nearest multiple of ALIGNMENT */
#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) // Size of pointer (Bytes)

/* Basic constants and macros */
#define WSIZE     4             /* Word and header/footer size (bytes) */
#define DSIZE     8             /* Double word size (bytes) */
#define CHUNKSIZE (1 << 12)     /* Extend heap by this amount (bytes) */
#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc)  ((size) | (alloc)) /* Pack a size and allocated bit into a word */

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)     ((char *)(bp) - WSIZE)
#define FTRP(bp)     ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

static char *heap_listp = NULL; /* Global variables */


/* internal helpers (prototypes) */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void  place(void *bp, size_t asize);


int mm_init(void)
{
    /* Create the initial empty heap */
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) return -1;
    PUT(heap_listp, 0);                           /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));  /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));  /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));      /* Epilogue header */
    heap_listp += (2*WSIZE);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));              /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));              /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));      /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}
void *mm_malloc(size_t size)
{
    size_t asize;       /* Adjusted block size */
    size_t extendsize;  /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if(size == 0) return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if(size <= DSIZE) asize = 2 * DSIZE;
    else asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    /* Search the free list for a fit */
    if((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize / WSIZE)) == NULL) return NULL;
    place(bp, asize);
    return bp;
}
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc) {                 /* Case 1 */
        return bp;
    }
    else if(prev_alloc && !next_alloc) {           /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if(!prev_alloc && next_alloc) {           /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else {                                          /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}
void *mm_realloc(void *bp, size_t size)
{
    if(bp == NULL) return mm_malloc(size);
    if(size == 0) {
        mm_free(bp);
        return NULL;
    }

    size_t outdatedSize = GET_SIZE(HDRP(bp));
    size_t adjustedSize;
    if(size <= DSIZE) adjustedSize = 2 * DSIZE;
    else adjustedSize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    if(adjustedSize <= outdatedSize) {
        size_t emptySize = outdatedSize - adjustedSize;
        if(emptySize >= 2 * DSIZE) {
            PUT(HDRP(bp), PACK(adjustedSize, 1));
            PUT(FTRP(bp), PACK(adjustedSize, 1));
            void *pEmptyBlock = NEXT_BLKP(bp);
            PUT(HDRP(pEmptyBlock), PACK(emptySize, 0));
            PUT(FTRP(pEmptyBlock), PACK(emptySize, 0));
            coalesce(pEmptyBlock);
        }
        return bp;
    }

    // Check if the adjacent block on the right side is free
    void *pAdjacentBlock = NEXT_BLKP(bp);
    if(!GET_ALLOC(HDRP(pAdjacentBlock))) {
        size_t capacity = outdatedSize + GET_SIZE(HDRP(pAdjacentBlock));
        if(capacity >= adjustedSize) {
            PUT(HDRP(bp), PACK(capacity, 1));
            PUT(FTRP(bp), PACK(capacity, 1));
            size_t emptyBlcokSize = capacity - adjustedSize;
            if(emptyBlcokSize >= 2 * DSIZE) {
                PUT(HDRP(bp), PACK(adjustedSize, 1));
                PUT(FTRP(bp), PACK(adjustedSize, 1));
                void *pEmptyBlock = NEXT_BLKP(bp);
                PUT(HDRP(pEmptyBlock), PACK(emptyBlcokSize, 0));
                PUT(FTRP(pEmptyBlock), PACK(emptyBlcokSize, 0));
            }
            return bp;
        }
    }

    void *pDetachedBlock = mm_malloc(size);
    if(pDetachedBlock == NULL) return NULL;
    size_t copyingSize = outdatedSize - DSIZE;
    if(size < copyingSize) copyingSize = size;
    memcpy(pDetachedBlock, bp, copyingSize);
    mm_free(bp);
    return pDetachedBlock;
}
static void *find_fit(size_t asize) {
  void *bp;
  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) return bp;
  }
  return NULL;
}
static void place(void *bp, size_t sizeToAllocate) {
  size_t sizeOfFreeBlock = GET_SIZE(HDRP(bp));
  if((sizeOfFreeBlock - sizeToAllocate) >= (2 * DSIZE)) {
    PUT(HDRP(bp), PACK(sizeToAllocate, 1));
    PUT(FTRP(bp), PACK(sizeToAllocate, 1));
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(sizeOfFreeBlock - sizeToAllocate, 0));
    PUT(FTRP(bp), PACK(sizeOfFreeBlock - sizeToAllocate, 0));
  } else {
    PUT(HDRP(bp), PACK(sizeOfFreeBlock, 1));
    PUT(FTRP(bp), PACK(sizeOfFreeBlock, 1));
  }
}
