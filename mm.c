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
    "team 2",
    /* First member's full name */
    "Lee na young / park do hyun / kim sang ho\n",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
// (4+7) & ~0x7 == 1011 & 1000 == 1000 == 8

#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) // size_t == unsigned int == 4bytes

// Basic constants and macros
#define WSIZE 4 // word and header/footer size (bytes)
#define DSIZE 8 // double word size (bytes)
#define CHUNKSIZE (1<<12) // extend heap by this amount (bytes) + this size reduce = 1<<10 → 84score

#define MAX(x, y) ((x)>(y) ? (x):(y))

// pack a size and allocated bit into a word
#define PACK(size, alloc) ((size) | (alloc))

// read and write a word at address p
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// read the size and allocated fields from address p
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

// given block ptr bp, compute address if its header and footer
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// given block ptr bp, compute address of next and previous blocks
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

// explicit free list use prec and succ
#define PREC_FREEP(bp) (*(void**)(bp)) // *(GET(PREC_FREEP(bp))) == prev free list's bp //Predecessor
#define SUCC_FREEP(bp) (*(void**)(bp + WSIZE)) // *(GET(SUCC_FREEP(bp))) == next free list's bp //successor


static void *heap_listp = NULL; //use heap_listp
// free list's first bp
static void *free_listp = NULL; //explicit free list use free_listp

// new return or create free block add free list's front
void put_free_block(void *bp){
    SUCC_FREEP(bp) = free_listp;
    PREC_FREEP(bp) = NULL;
    PREC_FREEP(free_listp) = bp;
    free_listp = bp;
}

// always free list's the tail of prologue block exist, so condition → simple
void remove_block(void *bp){
    //first block remove
    if (bp == free_listp){
        PREC_FREEP(SUCC_FREEP(bp)) = NULL;
        free_listp = SUCC_FREEP(bp);
    // front, back all exist
    } else {
        SUCC_FREEP(PREC_FREEP(bp)) = SUCC_FREEP(bp);
        PREC_FREEP(SUCC_FREEP(bp)) = PREC_FREEP(bp);
    }
}

static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // if (prev_alloc && next_alloc){ // case 1
    //     return bp;
    // }

    if (prev_alloc && !next_alloc){ // case 2
        remove_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) { // case 3
        remove_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        // PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        // bp = PREV_BLKP(bp);
    }

    else if (!prev_alloc && !next_alloc) { //case 4
        remove_block(PREV_BLKP(bp));
        remove_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        // bp = PREV_BLKP(bp);
    }
    put_free_block(bp);
    return bp;
}

static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    // allocate an even number of words to maintain alignment
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    // initialize free block header/footer and the epilogue header
    PUT(HDRP(bp), PACK(size, 0)); //free block header
    PUT(FTRP(bp), PACK(size, 0)); //free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); //new epilogue header

    // coalesce if the previous block was free
    return coalesce(bp);
}

/* 
 * mm_init - initialize the malloc package.
 */

int mm_init(void)
{
    // create the initial empty heap
    if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0); // alignment padding
    PUT(heap_listp + WSIZE, PACK(16,1)); //prologue header
    PUT(heap_listp + (2*WSIZE), NULL); //prologue prec pointer = null init
    PUT(heap_listp + (3*WSIZE), NULL); //prologue succ pointer = null init
    PUT(heap_listp + (4*WSIZE), PACK(16, 1)); //prologue footer
    PUT(heap_listp + (5*WSIZE), PACK(0, 1)); //epilogue header

    free_listp = heap_listp + DSIZE; //free_listp init


    // extend the empty heap with a free block of CHUNKSIZE bytes
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));

    // allocate block soon, free list inside remove
    remove_block(bp);

    if ((csize - asize) >= (2*DSIZE)){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        // free list's first put devide block
        put_free_block(bp);
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

static void *find_fit(size_t asize){
    // first-fit search
    void *bp;

    // free list's inside only allocated block is the tail of prologue block, so meet allocated block for-grammer is exit.
    for (bp = free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = SUCC_FREEP(bp)){
        if (asize <= GET_SIZE(HDRP(bp))) {
            return bp;
        }
    }
    return NULL; //no fit
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

void *mm_malloc(size_t size){

    size_t asize; //adjusted block size
    size_t extendsize; //amount to extend heap if no fit
    char *bp;

    //ignore spurious requests
    if (size == 0)
        return NULL;

    // adjust block size to include overhead and alignment reqs  
    asize = ALIGN(size + SIZE_T_SIZE);
    
    // search the free list for a fit
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    //no fit found. get more memory and place the block
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr){
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

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
    copySize = *(size_t *)((char *)oldptr - (SIZE_T_SIZE - 4));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}














// Perf index = 42 (util) + 40 (thru) = 82/100
