#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12) 
#define MAX(x, y) ((x) > (y)? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc)) 
#define GET(p)          (*(unsigned int *)(p)) 
#define PUT(p, val)     (*(unsigned int *)(p) = (val))  
#define GET_SIZE(p)     (GET(p) & ~0x7) 
#define GET_ALLOC(p)    (GET(p) & 0x1)
#define HDRP(bp)        ((char *)(bp) - WSIZE) // 
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 
#define PRED(bp)        ((char *)(bp))
#define SUCC(bp)        ((char *)(bp) + WSIZE)

#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 
//블록 최소 크기인 2**4부터 최대 크기인 2**32를 위한 리스트 29개
#define LIST_NUM 29

static void *extend_heap(size_t words);
void *mm_malloc(size_t size);
void mm_free(void *ptr);
static void *coalesce(void *bp);
void *mm_realloc(void *ptr, size_t size);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
void delete_block(char* bp);
void add_free_block(char* bp);
int get_seg_list_num(size_t size);

static char *heap_listp;
//분리 가용 리스트 생성
void* seg_list[LIST_NUM];

int mm_init(void)
{   
    //각 분리 가용 리스트를 NULL로 초기화해준다.
    for (int i = 0; i < LIST_NUM; i ++){
        seg_list[i] = NULL;
    }

    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) 
        return -1;

    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
        return -1;
    return 0;
}

static void *extend_heap(size_t words)
{   
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * DSIZE : words * DSIZE; 

    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0)); 
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}


void *mm_malloc(size_t size)
{   
    size_t asize;
    size_t extendsize;
    char *bp;
    
    if (size == 0)
        return NULL;
    
    if (size <= DSIZE)
        asize = 2*DSIZE; 
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE); 

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

void mm_free(void *bp)
{   
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));
    coalesce(bp);
}

static void *coalesce(void *bp)
{   
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); 
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        
        delete_block(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));

        delete_block(PREV_BLKP(bp));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else if (!prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))) + GET_SIZE(HDRP(PREV_BLKP(bp)));

        delete_block(PREV_BLKP(bp));
        delete_block(NEXT_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    
    add_free_block(bp);
    return bp;
}


void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

static void *find_fit(size_t asize)
{  
    void *search_p;
    //asize가 들어갈 수 있는 seg_list 찾기
    int i = get_seg_list_num(asize);
    
    //리스트 내부의 블록들 중 가장 작은 블록 할당(best-fit)
    void *tmp = NULL;
    while (i < LIST_NUM){
        for (search_p = seg_list[i]; search_p != NULL; search_p = GET(SUCC(search_p))){
            if (GET_SIZE(HDRP(search_p)) >= asize){
                if (tmp == NULL){
                    tmp = search_p;
                } else {
                    if (GET_SIZE(tmp) > GET_SIZE(HDRP(search_p))){
                        tmp = search_p;
                    }
                }
            }
        }
        if (tmp != NULL){
            return tmp;
        }
        i ++;
    }

    return NULL;
}

static void place(void *bp, size_t asize)
{   
    delete_block(bp);
    size_t old_size = GET_SIZE(HDRP(bp));
    if (old_size >= asize + (2 * DSIZE)){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        
        PUT(HDRP(NEXT_BLKP(bp)), PACK((old_size - asize), 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK((old_size - asize), 0));
        
        coalesce(NEXT_BLKP(bp));
    }
    else {
        PUT(HDRP(bp), PACK(old_size, 1));
        PUT(FTRP(bp), PACK(old_size, 1));
    }
}

void delete_block(char* bp){ 
    int seg_list_num = get_seg_list_num(GET_SIZE(HDRP(bp)));

    if (GET(PRED(bp)) == NULL){
        if (GET(SUCC(bp)) == NULL){
            seg_list[seg_list_num] = NULL;
        } else {
            PUT(PRED(GET(SUCC(bp))), NULL);
            seg_list[seg_list_num] = GET(SUCC(bp));
        }
    } 
    else {
        if (GET(SUCC(bp)) == NULL){
            PUT(SUCC(GET(PRED(bp))), NULL);
        } else {
            PUT(PRED(GET(SUCC(bp))), GET(PRED(bp)));
            PUT(SUCC(GET(PRED(bp))), GET(SUCC(bp)));
        }
    }
}

void add_free_block(char* bp){
    //들어가야 하는 seg_list 찾고 그 seg_list에 추가
    int seg_list_num = get_seg_list_num(GET_SIZE(HDRP(bp)));
    if (seg_list[seg_list_num] == NULL){
        PUT(PRED(bp), NULL);
        PUT(SUCC(bp), NULL);
    } else {
        PUT(PRED(bp), NULL);
        PUT(SUCC(bp), seg_list[seg_list_num]);
        PUT(PRED(seg_list[seg_list_num]), bp);
    }
    seg_list[seg_list_num] = bp;
}

int get_seg_list_num(size_t size){
    //seg_list[0]은 블록의 최소 크기인 2**4를 위한 리스트 
    int i = -4;
    while (size != 1){
        size = (size >> 1);
        i ++;
    }
    return i;
}
