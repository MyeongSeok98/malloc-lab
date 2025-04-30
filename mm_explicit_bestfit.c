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
    /* Team name */
    "ShinMyeong",
    /* First member's full name */
    "Kim Myeong Seok",
    /* First member's email address */
    "myong2404@gmail.com",
    /* Second member's full name (leave blank if none) */
    "Shin Dong Ju",
    /* Second member's email address (leave blank if none) */
    "madk"};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// 기본 상수와 매크로
#define WSIZE     4           /* 워드(word) 크기이자 헤더/푸터 크기 (바이트) */
#define DSIZE     8           /* 더블워드(double‐word) 크기 (바이트) */
#define CHUNKSIZE (1<<12)     /* 힙을 늘릴 때 한번에 요청하는 기본 단위 (4KB) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))
                   /* x, y 중 큰 값을 반환하는 간단한 매크로 */

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))
                   /* 블록 크기(size: 상위 비트)와 alloc 비트(하위 1비트)를 OR 연산 */

/* Read and write a word at address p */
#define GET(p)      (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
                   /* p가 가리키는 워드(4바이트)를 읽거나(val을) 써넣음 */

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
                   /* 
                     GET_SIZE: 하위 3비트(=정렬 용도/alloc 비트)를 지우고
                               블록 크기만 꺼내고,
                     GET_ALLOC: 최하위 비트만 꺼내어 alloc(0/1) 정보 확인
                   */

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
                   /* payload 포인터 bp에서 한 워드(-WSIZE) 이동 → 헤더 주소 */
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
                   /* 
                     bp에서 블록 전체 크기(GET_SIZE)만큼 이동하고,
                     푸터는 그 바로 앞(=끝에서 한 워드 뒤)니까 DSIZE(헤더+푸터 크기)만큼 빼 줌
                   */

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
                   /* 현재 블록 헤더에서 크기를 읽어 bp를 그만큼 앞으로 이동 → 다음 블록 payload 위치 */
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
                   /* 
                     bp에서 DSIZE(헤더+푸터)만큼 뒤로 가면
                     이전 블록 푸터 위치 → 그 값(GET_SIZE)만큼 더 뒤로 가면
                     이전 블록의 payload 시작 위치 
                   */

/* 명시적 가용리스트 */
#define GET_PRED(bp)        (*(void **)(bp))
#define GET_SUCC(bp)        (*(void **)((char *)(bp) + WSIZE))
static char* headp = NULL;
        
/*
 * mm_init - initialize the malloc package.
 */

static char* heap_listp;

static void insert_free_block(void *bp){
    GET_SUCC(bp) = headp;
    if (headp){
        GET_PRED(headp) = bp;
    }
    
    headp = bp;
}
static void remove_free_block(void *bp){
    if(bp == headp){
        headp = GET_SUCC(headp);
        return;
    }
    GET_SUCC(GET_PRED(bp)) = GET_SUCC(bp);

    if(GET_SUCC(bp) != NULL)
        GET_PRED(GET_SUCC(bp)) = GET_PRED(bp);
}

static void* collesce(void *bp){
    // 이전 블록 alloc 여부
    size_t prealloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    // 다음 블록 alloc 여부
    size_t nextalloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t thissize = GET_SIZE(HDRP(bp));

    size_t newsize;

    if(nextalloc && !prealloc){
        remove_free_block(PREV_BLKP(bp));
        newsize = thissize + GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(newsize, 0));
        PUT(FTRP(bp), PACK(newsize, 0));
        bp = PREV_BLKP(bp);
    }
    else if(!nextalloc && prealloc){
        remove_free_block(NEXT_BLKP(bp));
        newsize = thissize + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(newsize, 0));
        PUT(FTRP(bp), PACK(newsize, 0));
    }
    else if (!nextalloc && !prealloc){
        remove_free_block(PREV_BLKP(bp));
        remove_free_block(NEXT_BLKP(bp));
        newsize = thissize + GET_SIZE(FTRP(NEXT_BLKP(bp))) + GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(newsize, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(newsize, 0));
        bp = PREV_BLKP(bp);
    }

    insert_free_block(bp);
    return bp;
}


static void* extend_heap(size_t words){
    char* bp;
    size_t size;

    if(words % 2 == 0){
        size = words * WSIZE;
    }
    else{
        size = (words + 1) * WSIZE;                                                                                                 
    }
    
    if((long)(bp = mem_sbrk(size)) == -1){
        return NULL;
    }

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    // 에필로그 정하기
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));

    return collesce(bp);
}

int mm_init(void) {   
    if ((heap_listp = mem_sbrk(8 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp + (0 * WSIZE), 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(2 * DSIZE, 0));
    PUT(heap_listp + (4 * WSIZE), NULL);
    PUT(heap_listp + (5 * WSIZE), NULL);
    PUT(heap_listp + (6 * WSIZE), PACK(2 * DSIZE, 0));
    PUT(heap_listp + (7 * WSIZE), PACK(0, 1));

    heap_listp += (2 * DSIZE);
    headp = heap_listp;
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    
    return 0;
}

void *place(void *bp, size_t size){
    size_t currentsize = GET_SIZE(HDRP(bp));

    /* 명시적 부분 */
    remove_free_block(bp);
    /* 명시적 부분 끝*/
    if((currentsize - size) >= (2 * DSIZE)){
        PUT(HDRP(bp), PACK(size, 1));
        PUT(FTRP(bp), PACK(size, 1));
        void *newbp = (char *)bp + size;
        PUT(HDRP(newbp), PACK(currentsize - size, 0));
        PUT(FTRP(newbp), PACK(currentsize - size, 0));

        insert_free_block(newbp);
    }
    else{
        PUT(HDRP(bp), PACK(currentsize, 1));
        PUT(FTRP(bp), PACK(currentsize, 1));
    } 
} 

void *find_fit(size_t size){
    char *bp = headp;
    char *targetp = NULL;
    size_t mingap = 100000000; 
    while(bp != NULL){
        if(GET_SIZE(HDRP(bp)) >= size){
            size_t gap = GET_SIZE(HDRP(bp)) - size;
            if(gap < mingap)
                targetp = bp;
                mingap = gap;
        }
        bp = GET_SUCC(bp);
    }
    if(targetp) return targetp;
    return NULL;                                      
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{   
    size_t newsize;
    char *bp;
    if( size == 0)
        return NULL;
    
    if (size <= DSIZE)
        newsize = 2 * DSIZE;
    else
        newsize = DSIZE * ((size + 2 * DSIZE - 1) / DSIZE);

    if((bp = find_fit(newsize)) != NULL){
        place(bp, newsize);
        return bp;
    }
    size_t extendsize = MAX(newsize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) {                   // 실패 시 bp로는 NULL을 반환한다.
        return NULL;
    }

    place(bp, newsize);

    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    PUT(HDRP(bp), PACK(GET_SIZE(HDRP(bp)), 0));
    PUT(FTRP(bp), PACK(GET_SIZE(HDRP(bp)), 0));

    collesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size) {
    void *oldptr = ptr;                                                     // 크기를 조절하고 싶은 힙의 시작 포인터
    void *newptr;                                                           // 크기 조절 뒤의 새 힙의 시작 포인터
    size_t copySize;                                                        // 복사할 힙의 크기
    
    newptr = mm_malloc(size);                                               // place를 통해 header, footer가 배정된다.
    if (newptr == NULL) {
        return NULL;
    }
    
    copySize = GET_SIZE(HDRP(oldptr));                                      // 원래 블록의 사이즈
    
    if (size < copySize) {                                                  // 만약 블록의 크기를 줄이는 것이라면 size만큼으로 줄이면 된다. copySize - size 공간의 데이터는 잘리게 된다. 밑의 memcpy에서 잘린 만큼의 데이터는 복사되지 않는다.
        copySize = size;
    }
    
    memcpy(newptr, oldptr, copySize);                                       // oldptr부터 copySize까지의 데이터를, newptr부터 심겠다.
    mm_free(oldptr);                                                        // 기존 oldptr은 반환한다.
    return newptr;
}