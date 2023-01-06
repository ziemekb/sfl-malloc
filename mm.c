/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  Blocks are never coalesced or reused.  The size of
 * a block is found at the first aligned word before the block (we need
 * it for realloc).
 *
 * This code is correct and blazingly fast, but very bad usage-wise since
 * it never frees anything.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>
#include <limits.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
#define debug(...) printf(__VA_ARGS__)
#else
#define debug(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */


/* Basic constants and macros */
#define WSIZE 4 /* Word size*/
#define DSIZE 8 /* Double word size*/
#define CHUNKSIZE (1<<12) /* Size of memory chunk*/

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_PREVFREE(p) (GET(p) & 0x2)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, read pointers to next and previous free blocks in segregated free list */
#define NEXT_FREE_BLKP(bp) (*(void **)(bp))
#define PREV_FREE_BLKP(bp) (*((void **)((char *)(bp) + WSIZE)))

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

#define ROUND(size) ((size + ALIGNMENT - 1) & -ALIGNMENT)

#define SINGULAR_BLOCKS_NUM 16 // 
#define RANGED_BLOCKS_NUM 5 //
#define LOWEST_LEADING_ZEROS 23 // __builtin_clz(256) = 23 in unsigned 32 bit 

static char *heap_start; /* Address of the prologue footer */
static char *last;       /* Points at epilogue header */

/*
 * segregated free lists in which free blocks ranging 
 * in size from 16 to 256 bytes have its own list
 */

static void *segregated_list[SINGULAR_BLOCKS_NUM + RANGED_BLOCKS_NUM]; // = { NULL }; 

static inline int find_index(size_t size) {

  if(size <= SINGULAR_BLOCKS_NUM * ALIGNMENT) {
    return size / 16 - 1; 
  }

  return __builtin_clz(size) - LOWEST_LEADING_ZEROS + SINGULAR_BLOCKS_NUM - 1;
}

static inline void *find_block(size_t size) {
 
  int index = find_index(size); // smallest index that may fit the block
  int range = SINGULAR_BLOCKS_NUM + RANGED_BLOCKS_NUM;

  for(; index < range; ++index) {

    void *new_block_ptr = segregated_list[index];

    if(!new_block_ptr) {
      continue;
    }
        
    if(GET_SIZE(HDRP(new_block_ptr)) == size) {
      // here i should get next free block of this size to be the first 
      // or mark segregated_list[index] as NULL if none free are left
      
      segregated_list[index] = NEXT_FREE_BLKP(new_block_ptr);
       
      if(segregated_list[index]) {
        PREV_FREE_BLKP(segregated_list[index]) = NULL;
      }

      return new_block_ptr;
    }
    
    int min_diff = INT_MAX;
    void *min_ptr = new_block_ptr;
     
    while(new_block_ptr) {
      int diff = GET_SIZE(HDRP(new_block_ptr)) - size; // diff can be negative !!!
      
      if(diff < min_diff) {
        min_diff = diff;
        min_ptr = new_block_ptr;
      }
      new_block_ptr = NEXT_FREE_BLKP(new_block_ptr); 
    }
    void *prev_ptr = PREV_FREE_BLKP(min_ptr);
    void *next_ptr = NEXT_FREE_BLKP(min_ptr);
    
    if(prev_ptr) {
      NEXT_FREE_BLKP(prev_ptr) = next_ptr;
    }
    
    if(next_ptr) {
      PREV_FREE_BLKP(next_ptr) = prev_ptr;
    }
    
    if(min_diff >= 0) {
      return min_ptr;
    }
  }

  return NULL;
}

/*
 * coalesce - Possibly coalesce adjecent blocks
 */
static void *coalesce(void *ptr) {

  size_t prev_alloc = GET_ALLOC(ptr - DSIZE);
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
  size_t size = GET_SIZE(HDRP(ptr));

  if (prev_alloc && next_alloc) { // previous and next blocks are allocated
    return ptr;
  } else if (prev_alloc && !next_alloc) { // next block is free
    size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
  } else if (!prev_alloc && next_alloc) { // previous block is free
    size += GET_SIZE(ptr - DSIZE);
    PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    ptr = PREV_BLKP(ptr);
  } else { // both previous and next blocks are free
    size += GET_SIZE(ptr - DSIZE);
    size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
    PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));
    ptr = PREV_BLKP(ptr);
  }

  return ptr;
}

/*
 * mm_init - Called when a new trace starts.
 */
int mm_init(void) {

  if ((heap_start = mem_sbrk(4 * WSIZE)) < 0) {
    return -1;
  }

  PUT(heap_start, 0);                            /* Alignment padding */
  PUT(heap_start + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
  PUT(heap_start + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
  PUT(heap_start + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
  heap_start += (2 * WSIZE);
  last = heap_start + WSIZE;

  return 0;
}

/*
 * malloc - Allocate a block by incrementing the brk pointer.
 *      Always allocate a block whose size is a multiple of the alignment.
 */
void *malloc(size_t size) {

  if (size + DSIZE < ALIGNMENT) {
    size = ALIGNMENT;
  } else {
    size = ROUND(size + DSIZE);
  }

  char *ptr = heap_start + DSIZE;

  while (ptr < last) {

    size_t ptr_size = GET_SIZE(HDRP(ptr));

    if (GET_ALLOC(HDRP(ptr))) { // if block is not free skip
      ptr += ptr_size;
      continue;
    }

    if (ptr_size >= size) { // the block is sufficient size

      if (ptr_size - size < ALIGNMENT) { // minimal size requirment
        PUT(HDRP(ptr), PACK(ptr_size, 1));
        PUT(FTRP(ptr), PACK(ptr_size, 1));
      } else {                         // splitting
        PUT(HDRP(ptr), PACK(size, 1)); // allocated block header
        PUT(FTRP(ptr), PACK(size, 1)); // allocated block footer
        PUT(HDRP(NEXT_BLKP(ptr)),
            PACK(ptr_size - size, 0)); // free block header
        PUT(FTRP(NEXT_BLKP(ptr)),
            PACK(ptr_size - size, 0)); // free block footer
      }

      return ptr;
    }

    /* the block is not sufficient size but maybe coalescence is possible */
    size_t new_block_size = GET_SIZE(HDRP(coalesce(ptr)));

    while (new_block_size != ptr_size) {

      if (new_block_size >=
          size) { // newly coalescenced block has sufficient size
        PUT(HDRP(ptr), PACK(new_block_size, 1));
        PUT(FTRP(ptr), PACK(new_block_size, 1));
        return ptr;
      }

      ptr_size = new_block_size;
      new_block_size = GET_SIZE(HDRP(coalesce(ptr)));
    }

    ptr += ptr_size;
  }

  char *new_block = mem_sbrk(size);

  PUT(HDRP(new_block), PACK(size, 1));
  PUT(FTRP(new_block), PACK(size, 1));
  last = HDRP(NEXT_BLKP(new_block));
  PUT(last, PACK(0, 1)); // new epilogue header

  return new_block;
}

/*
 * free - We don't know how to free a block.  So we ignore this call.
 *      Computers have big memories; surely it won't be a problem.
 */
void free(void *ptr) {

  if (ptr == NULL) {
    return;
  }

  size_t size = GET_SIZE(HDRP(ptr));

  PUT(HDRP(ptr), PACK(size, 0));
  PUT(FTRP(ptr), PACK(size, 0));
}

/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block.
 */
void *realloc(void *old_ptr, size_t size) {
  /* If size == 0 then this is just free, and we return NULL. */
  if (size == 0) {
    free(old_ptr);
    return NULL;
  }

  /* If old_ptr is NULL, then this is just malloc. */
  if (!old_ptr)
    return malloc(size);

  void *new_ptr = malloc(size);

  /* If malloc() fails, the original block is left untouched. */
  if (!new_ptr)
    return NULL;

  /* Copy the old data. */
  size_t old_size = GET_SIZE(HDRP(old_ptr));
  if (size < old_size)
    old_size = size;
  memcpy(new_ptr, old_ptr, old_size);

  /* Free the old block. */
  free(old_ptr);

  return new_ptr;
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);

  /* If malloc() fails, skip zeroing out the memory. */
  if (new_ptr)
    memset(new_ptr, 0, bytes);

  return new_ptr;
}

/*
 * mm_checkheap - So simple, it doesn't need a checker!
 */
void mm_checkheap(int verbose) {
}
