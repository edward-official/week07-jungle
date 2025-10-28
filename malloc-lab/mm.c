/*
 * mm-seg-explicit.c - Segregated explicit free lists (doubly linked)
 *
 * - 여러 개의 size group을 두고, 각 group마다 explicit free list를 유지
 * - free 블록 payload에 pred/succ 포인터(각 8B)를 저장 (총 16B)
 * - 삽입: 해당 group 헤드에 LIFO
 * - 검색: 요청 크기에 해당하는 group부터 위로 올라가며 first-fit (옵션: 동일 group 내 best-fit)
 * - 병합(coalesce) 시 이웃 free 블록을 리스트에서 제거 → 사이즈 합치기 → 새 사이즈 group에 재삽입
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
    "Krafton Jungle 11",
    "Jongyun Lee",
    "openmoresome@gmail.com",
    "",
    "",
};

/* Alignment / size helpers */
#define ALIGNMENT 8
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE       4               /* header/footer word size */
#define DSIZE       8               /* double word */
#define CHUNKSIZE   (1 << 12)       /* heap extend size: 4KB (init-time) */
#define MAX(x,y)    ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

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

/* Free block payload: pred/succ pointers (each 8B on 64-bit) */
#define PRED_PTR(bp) ((char **)(bp))
#define SUCC_PTR(bp) ((char **)((char *)(bp) + DSIZE))

#define GET_PRED(bp) (*(char **)(PRED_PTR(bp)))
#define GET_SUCC(bp) (*(char **)(SUCC_PTR(bp)))
#define SET_PRED(bp, ptr) (GET_PRED(bp) = (char *)(ptr))
#define SET_SUCC(bp, ptr) (GET_SUCC(bp) = (char *)(ptr))

/* Minimum free block size: hdr(4)+ftr(4)+pred(8)+succ(8)=24 */
#define MIN_FREE_BLK (ALIGN(WSIZE + WSIZE + DSIZE + DSIZE))  /* 24 */

/* Segregated list config */
#define NLISTS 16

/* Globals */
static char *pPrologueData = NULL;   /* prologue payload pointer */
static char *headers[NLISTS];        /* heads of segregated explicit free lists */

/* Internal helpers (prototypes) */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void  place(void *bp, size_t asize);

static void  insert_node(void *bp);
static void  remove_node(void *bp);
static int   size_to_group(size_t size);

/* policy helpers */
static size_t getFreeSizeOfTail(void);

/* Map size → group index (대략 24,32,48,64,96,128,192,... 2배 근사) */
static int size_to_group(size_t size)
{
    /* size는 헤더 포함 블록 크기 */
    if (size <= 32) return 0;           /* 24~32 */
    if (size <= 48) return 1;           /* 33~48 */
    if (size <= 64) return 2;           /* 49~64 */
    if (size <= 96) return 3;           /* 65~96 */
    if (size <= 128) return 4;          /* 97~128 */
    if (size <= 192) return 5;          /* 129~192 */
    if (size <= 256) return 6;
    if (size <= 384) return 7;
    if (size <= 512) return 8;
    if (size <= 768) return 9;
    if (size <= 1024) return 10;
    if (size <= 1536) return 11;
    if (size <= 2048) return 12;
    if (size <= 4096) return 13;
    if (size <= 8192) return 14;
    return 15;                          /* 8193+ */
}

int mm_init(void)
{
    /* 초기화: prologue(8B) + epilogue(4B) 프롤로그 설정 */
    if ((pPrologueData = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(pPrologueData, 0);                            /* alignment padding */
    PUT(pPrologueData + (1 * WSIZE), PACK(DSIZE, 1)); /* prologue header */
    PUT(pPrologueData + (2 * WSIZE), PACK(DSIZE, 1)); /* prologue footer */
    PUT(pPrologueData + (3 * WSIZE), PACK(0, 1));     /* epilogue header */
    pPrologueData += (2 * WSIZE);

    for (int i = 0; i < NLISTS; ++i)
        headers[i] = NULL;

    /* 초기 부트스트랩: 첫 free 블록을 만들기 위해 CHUNKSIZE만큼 확장 */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* 8바이트 정렬 보장: 짝수 워드로 반올림 */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));              /* free block header */
    PUT(FTRP(bp), PACK(size, 0));              /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));      /* new epilogue header */

    return coalesce(bp);
}

/* Insert at head of segregated list */
static void insert_node(void *pJoiningNode)
{
    size_t size = GET_SIZE(HDRP(pJoiningNode));
    int group = size_to_group(size);
    SET_PRED(pJoiningNode, NULL);
    SET_SUCC(pJoiningNode, headers[group]);
    if (headers[group] != NULL)
        SET_PRED(headers[group], pJoiningNode);
    headers[group] = (char *)pJoiningNode;
}

/* Remove from its segregated list */
static void remove_node(void *pTargetNode)
{
    size_t size = GET_SIZE(HDRP(pTargetNode));
    int group = size_to_group(size);

    char *pred = GET_PRED(pTargetNode);
    char *succ = GET_SUCC(pTargetNode);

    if (pred != NULL)
        SET_SUCC(pred, succ);
    else
        headers[group] = succ;

    if (succ != NULL)
        SET_PRED(succ, pred);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

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

    insert_node(bp);
    return bp;
}

/* 힙 끝단(epilogue 바로 앞)의 free 블록 크기 반환, 없으면 0 */
static size_t getFreeSizeOfTail(void)
{
    /* mem_heap_hi()는 힙의 마지막 유효 바이트를 가리킴 */
    char *pEpliogueHeader = (char *)mem_heap_hi() + 1 - WSIZE;   /* epilogue header 주소 */
    char *pFooterOfLeftAdjacent = pEpliogueHeader - WSIZE;       /* 직전 블록 footer */
    size_t sizeOfLeftAdjacent = GET_SIZE(pFooterOfLeftAdjacent);
    char *pLeftAdjacent = pFooterOfLeftAdjacent + DSIZE - sizeOfLeftAdjacent;       /* 직전 블록 bp */
    int isLeftAdjacentAllocated = GET_ALLOC(HDRP(pLeftAdjacent));
    return isLeftAdjacentAllocated ? 0 : sizeOfLeftAdjacent;
}

void *mm_malloc(size_t size)
{
    size_t adjustedSize;
    char *bp;

    if (size == 0) return NULL;

    /* 헤더/풋터 및 정렬 반영한 유효 크기 계산 */
    if (size <= DSIZE) adjustedSize = 2 * DSIZE;
    else adjustedSize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    if (adjustedSize < MIN_FREE_BLK) adjustedSize = MIN_FREE_BLK; /* MIN_FREE_BLK==24 */

    /* 1) 기존 가용 블록에서 먼저 시도 */
    if ((bp = find_fit(adjustedSize)) != NULL) {
        place(bp, adjustedSize);
        return bp;
    }

    /* 2) 끝단 free 블록의 부족분만 확장 (CHUNKSIZE 하한 없음) */
    size_t freeSizeOfTail = getFreeSizeOfTail();                 /* 없으면 0 */
    size_t lackingSize = (adjustedSize > freeSizeOfTail) ? (adjustedSize - freeSizeOfTail) : 0;
    if (lackingSize > 0) {
        /* 바이트 → 워드; extend_heap이 짝수 워드 정렬을 보장 */
        size_t nWord = (lackingSize + (WSIZE - 1)) / WSIZE;
        if (extend_heap(nWord) == NULL)
            return NULL;
    }

    /* 3) 확장/병합 이후엔 반드시 적합 블록이 존재해야 함 */
    bp = find_fit(adjustedSize);
    place(bp, adjustedSize);
    return bp;
}

void mm_free(void *bp)
{
    if (bp == NULL) return;

    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    SET_PRED(bp, NULL);
    SET_SUCC(bp, NULL);

    coalesce(bp);
}

void *mm_realloc(void *bp, size_t size)
{
    if (bp == NULL) return mm_malloc(size);
    if (size == 0) { mm_free(bp); return NULL; }

    size_t outdatedSize = GET_SIZE(HDRP(bp));
    size_t adjustedSize;
    if (size <= DSIZE) adjustedSize = 2 * DSIZE;
    else adjustedSize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    if (adjustedSize < MIN_FREE_BLK) adjustedSize = MIN_FREE_BLK;

    /* 축소 혹은 자투리 분할 */
    if (adjustedSize <= outdatedSize) {
        size_t sizeOfRightPiece = outdatedSize - adjustedSize;
        if (sizeOfRightPiece >= MIN_FREE_BLK) {
            PUT(HDRP(bp), PACK(adjustedSize, 1));
            PUT(FTRP(bp), PACK(adjustedSize, 1));
            void *nbp = NEXT_BLKP(bp);
            PUT(HDRP(nbp), PACK(sizeOfRightPiece, 0));
            PUT(FTRP(nbp), PACK(sizeOfRightPiece, 0));
            SET_PRED(nbp, NULL);
            SET_SUCC(nbp, NULL);
            coalesce(nbp);
        }
        return bp;
    }

    /* 우측 인접 free와 병합해 확장 시도 */
    void *pRightAdjacent = NEXT_BLKP(bp);
    if (!GET_ALLOC(HDRP(pRightAdjacent))) {
        size_t capacity = outdatedSize + GET_SIZE(HDRP(pRightAdjacent));
        if (capacity >= adjustedSize) {
            remove_node(pRightAdjacent);

            size_t sizeOfRightPart = capacity - adjustedSize;
            PUT(HDRP(bp), PACK(capacity, 1));
            PUT(FTRP(bp), PACK(capacity, 1));

            if (sizeOfRightPart >= MIN_FREE_BLK) {
                PUT(HDRP(bp), PACK(adjustedSize, 1));
                PUT(FTRP(bp), PACK(adjustedSize, 1));
                void *nbp = NEXT_BLKP(bp);
                PUT(HDRP(nbp), PACK(sizeOfRightPart, 0));
                PUT(FTRP(nbp), PACK(sizeOfRightPart, 0));
                SET_PRED(nbp, NULL);
                SET_SUCC(nbp, NULL);
                insert_node(nbp);
            }
            return bp;
        }
    }

    /* 새로 할당 후 복사 */
    void *pDestination = mm_malloc(size);
    if (pDestination == NULL) return NULL;

    size_t sizeOfPayload = outdatedSize - DSIZE; /* payload = block size - hdr(4) - ftr(4) */
    if (size < sizeOfPayload) sizeOfPayload = size;
    memcpy(pDestination, bp, sizeOfPayload);
    mm_free(bp);
    return pDestination;
}

/* Best-fit over segregated lists:
 * - 요청 크기의 group부터 위로 올라가며 모든 후보를 스캔
 * - waste(= 블록크기 - asize)가 가장 작은 블록을 선택
 * - 완벽 일치(gsize == asize)를 찾으면 즉시 반환
 */
static void *find_fit(size_t adjustedSize)
{
    void *pBestFit = NULL;
    size_t bestAmountOfWaste = (size_t)-1;  /* 가장 작은 낭비를 추적 */

    for (int group = size_to_group(adjustedSize); group < NLISTS; ++group) {
        for (char *bp = headers[group]; bp != NULL; bp = GET_SUCC(bp)) {
            size_t capacity = GET_SIZE(HDRP(bp));
            if (capacity >= adjustedSize) {
                size_t temp = capacity - adjustedSize;
                if (temp == 0) {
                    /* 완벽 일치: 더 볼 필요 없음 */
                    return bp;
                }
                if (temp < bestAmountOfWaste) {
                    bestAmountOfWaste = temp;
                    pBestFit = bp;
                }
            }
        }
    }

    return pBestFit; /* 없으면 NULL */
}


static void place(void *bp, size_t adjustedSize)
{
    size_t capacity = GET_SIZE(HDRP(bp));
    remove_node(bp);

    if (capacity - adjustedSize >= MIN_FREE_BLK) {
        /* 앞쪽을 할당, 뒤쪽을 free로 분할 */
        PUT(HDRP(bp), PACK(adjustedSize, 1));
        PUT(FTRP(bp), PACK(adjustedSize, 1));

        void *pRightPart = NEXT_BLKP(bp);
        size_t sizeOfRightPart = capacity - adjustedSize;
        PUT(HDRP(pRightPart), PACK(sizeOfRightPart, 0));
        PUT(FTRP(pRightPart), PACK(sizeOfRightPart, 0));
        SET_PRED(pRightPart, NULL);
        SET_SUCC(pRightPart, NULL);
        insert_node(pRightPart);
    } else {
        PUT(HDRP(bp), PACK(capacity, 1));
        PUT(FTRP(bp), PACK(capacity, 1));
    }
}
