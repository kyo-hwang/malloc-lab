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
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};
//내 추측으로는 가상 메모리는 이미 프로세스에게 주어진다. 동적 메모리 할당기는 이 가상 메모리의 힙 영역을 관리한다.
//동적 메모리 할당기는 힙 영역을 확장하거나 축소해야하는데 이것은 커널의 brk변수를 기준으로 확장한다.
//이 과제에서는 시스템 콜을 통해 커널에게 커널 변수인 brk를 확장하는 시스템 콜을 사용하지 않고, malloc으로 할당한 힙 영역에 응용 수준에서 선언한 brk함수로 heap을 확장한다고 가정하는 것 같다.
//즉 실제로 가상 메모리의 힙 영역을 증가시키지는 않는 것 같다.

    /* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*Basic constants and macros*/
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)

#define MAX(x,y) ((x)>(y)?(x):(y))

/*Pack a Szie and allocated bit into a word, size단위는 바이트, alloc은 1은 할당 0은 가용 상태*/
//헤더나 풋터에 넣을 정보를 만든다.
#define PACK(size,alloc) ((size)|(alloc))

/*Read and Write a word at address *p*/
#define GET(p) (*(unsigned int*)(p))
#define PUT(p,val) (*(unsigned int*)(p) = (val))

/*크기나 할당 상태를 얻는다.*/
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0X1)

/*블록 포인트 bp에 대해서 헤더나 풋터에 대한 포인터를 얻는다*/
#define HDRP(bp) ((char *)(bp) -WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) -DSIZE)

/*전 블록이나 다음 블록에 대한 포인터를 얻는다.*/
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char*)(bp)-DSIZE)))

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
/* 
 * mm_init - initialize the malloc package.
 sbrk함수 호출로 4워드의 공간을 먼저 확보한다.
 맨 앞 패딩 블록 1개
 prolog header footer 블록 각 한 개씩 총 2개
 epilog 블록 1개 초기화
 sbrk함수를 호출해서 초기 힙의 영역을 확장시켜야겠지
 */

static char* heap_listp;

int mm_init(void)
{ 
    if((heap_listp = mem_sbrk(4*WSIZE))==(void *)-1)
        return -1;
    PUT(heap_listp,0);
    PUT(heap_listp+(1*WSIZE),PACK(DSIZE, 1));
    PUT(heap_listp+(2*WSIZE),PACK(DSIZE, 1));
    PUT(heap_listp+(3*WSIZE),PACK(0,1));
    heap_listp += (2*WSIZE);

    if(extend_heap(CHUNKSIZE/WSIZE)==NULL){
        return -1;
    }
    return 0;
}

//힙을 확장하고 확장된 가용 블록을 등록한다.
static void * extend_heap(size_t words){
    char *bp;
    size_t size;

    size = (words %2) ? (words+1) *WSIZE : words*WSIZE;
    if((long)(bp = mem_sbrk(size))==-1){
        return NULL;
    }

    PUT(HDRP(bp),PACK(size,0));
    PUT(FTRP(bp),PACK(size,0));
    //에필로그 추가, 힙의 마지막을 추적하기 위해 heap_listp에 epilog 추가
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1));

    return coalesce(bp);
}

//반환된 블록 옆에 빈 리스트가 있다면 하나의 블록으로 합쳐준다.
//양 옆에 가용 리스트가 없는 경우, 오른쪽에 있는 경우, 왼쪽에 있는 경우, 둘 다 있는 경우로 나눌 수 있다.
static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));//HDRP라도 문제 없나??
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc){
        return bp;
    }
    else if(prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp),PACK(size,0));
        PUT(FTRP(bp),PACK(size,0));
    }
    else if(!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp),PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    else{
        size += GET_SIZE(HDRP(PREV_BLKP(bp)))+GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

//현재 블록을 할당으로 바꾸고 size값 설정, 그리고 분할 그런데 만약 남은 가용 공간 크기가 2워드보다 작거나 같다면 분할x
void place(void *bp,size_t asize){
    char* header = HDRP(bp);
    size_t size = GET_SIZE(header);
    //같다면 할당 번호만 1로 바꿔준다.
    if(size == asize){
        // printf("full_size : %d, alloc_size : %d header: %p footer: %p\n",size,asize,HDRP(bp),FTRP(bp));
        PUT(header,PACK(size,1));
        PUT(FTRP(bp),PACK(size,1));
    }
    //다르다면 분할, 
    else{
        // printf("full size : %d header: %p block_size: %d  footer: %p\n",size,HDRP(bp),GET_SIZE(HDRP(bp)),FTRP(bp));
        PUT(header,PACK(asize,1));
        PUT(FTRP(bp),PACK(asize,1));
        char* remain = NEXT_BLKP(bp);
        // printf("alloc_size : %d header: %p block_size: %d alloc:%d footer: %p\n",asize,HDRP(bp),GET_SIZE(HDRP(bp)),GET_ALLOC(HDRP(bp)),FTRP(bp));
        PUT(HDRP(remain),size-asize);
        PUT(FTRP(remain),size-asize);
        // printf("remain header : %p size: %d footer :%p\n", HDRP(remain), GET_SIZE(HDRP(remain)), FTRP(remain));
    }
}

//현재 블록이 size보다 크고, 가용 블록이면 할당 아니라면 다음 블록으로 이동, 만약 다음 블록의 헤더를 봤는데 block size가 0으로 되어있다면 null return
void* find_fit(size_t asize){
    char* curBlock = heap_listp + DSIZE;
    //다음 블록의 헤더가 0이 아니면 계속
    // printf("사ㅣ이즈 %d\n",GET_SIZE(HDRP(NEXT_BLKP(curBlock))));
    while(GET_SIZE(HDRP(curBlock))!=0){
        // printf("cur header : %p size: %d alloc:%d footer :%p\n", HDRP(curBlock), GET_SIZE(HDRP(curBlock)), GET_ALLOC(HDRP(curBlock)), FTRP(curBlock));
        if(GET_SIZE(HDRP(curBlock))>=asize && GET_ALLOC(HDRP(curBlock))==0){
            return curBlock;
        }
        curBlock = NEXT_BLKP(curBlock);
        // printf("가용공간 %d, 원하는 크기%d\n",GET_SIZE(HDRP(curBlock)),asize);
    }
    return NULL;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if(size == 0){
        return NULL;
    }

    //블럭 사이즈 결정하기
    if(size <= DSIZE){
        asize = 2*DSIZE;
    }
    else{
        //하나의 DSIZE는 header와 footer를 위한 것, DSIZE-1은 8의 배수이면서 크면서 가장 가까운 수를 구하기 위함.
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1))/DSIZE);
    }

    if((bp = find_fit(asize)) != NULL){
        place(bp,asize);
        return bp;
    }

    extendsize = MAX(asize,CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE))==NULL){
        return NULL;
    }
    place(bp,asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr),PACK(size,0));
    PUT(FTRP(ptr),PACK(size,0));
    coalesce(ptr);
}

int a = 0;
/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = GET_SIZE(HDRP(oldptr)) - 2*WSIZE;

    if (size < copySize)
      copySize = size;

    memcpy(newptr, oldptr, copySize);

    mm_free(oldptr);
    return newptr;
}










