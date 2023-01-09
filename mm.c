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
#define PSIZE 8 /* Size of pointer in bytes */
#define CHUNKSIZE (1<<12) /* Size of memory chunk*/

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* calulate distance between two base pointers with one unit being equal to ALIGNMENT*/
#define DISTANCE_BETWEEN(p1, p2) ((p1 && p2) ? (p1 - p2) / ALIGNMENT : 0)
/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define GETS(p) (*(int *)(p)) // read signed integer value
#define GETP(p) (*(void **)(p)) // read pointer from adress p
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define PUTS(p, val) (*(int *)(p) = (val)) // write signed integer value
#define PUTP(p, pval) (*(void **)(p) = (pval)) // write a pointer at address p

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of its previous free block field */
#define PREV_FIELD(bp) ((char *)(bp) + WSIZE)

/* Given block ptr bp, read pointers to the next free block in segregated free list */
#define NEXT_FREE_BLKP(bp) (GETS(bp) ? (void *)((char *)(bp) + GETS(bp) * ALIGNMENT) : NULL)
#define PREV_FREE_BLKP(bp) (GETS(PREV_FIELD(bp)) ? (void *)((char *)(bp) + GETS(PREV_FIELD(bp)) * ALIGNMENT) : NULL)

/* Add n * PSIZE bytes to void pointer since void pointer arthimetic is illegal and sizeof(void *) = PSIZE */
#define ADD_VOIDP(p, n) ((void *)((char *)(p) + PSIZE * n))

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define ROUND(size) ((size + ALIGNMENT - 1) & -ALIGNMENT)

#define SINGULAR_BLOCKS_NUM 16 // Number of free lists with blocks of its own sizes
#define RANGED_BLOCKS_NUM 8 // Number of free lists with blocks in a size classes

/* Number of all free lists */
#define SFL_SIZE (SINGULAR_BLOCKS_NUM + RANGED_BLOCKS_NUM)

/* Number of leading zeros defining limits of size classes in segregated free lists */
#define LOWEST_LEADING_ZEROS __builtin_clz(256) // 23 in 32 bit int 
#define HIGHEST_LEADING_ZEROS __builtin_clz(32768) // 16 in 32 bit int

static char *heap_start; /* Address of the prologue footer */
static char *last;       /* Points at epilogue header */
static void *sfl_start;   /* Adress of first list in segregated free lists*/

/*
 * segregated free lists in which free blocks ranging 
 * in size from 16 to 256 bytes have its own list
 * and the rest is put into power of two size classes 
 */

static inline int find_index(size_t size) {

  int leading_zeros = __builtin_clz(size);

  if(size <= SINGULAR_BLOCKS_NUM * ALIGNMENT) {
    return (size / ALIGNMENT) - 1; 
  } else if (leading_zeros <= HIGHEST_LEADING_ZEROS) {
    return SFL_SIZE - 1;
  }
  
  return LOWEST_LEADING_ZEROS - leading_zeros + SINGULAR_BLOCKS_NUM;
}

/*
 * remove_from_sfl - Remove block from segregated free list
 */
static inline void remove_from_sfl(void *ptr, int index) {
  
  if(ptr == NULL) {
    return;
  }

  void *next_free_blkp = NEXT_FREE_BLKP(ptr);
  void *prev_free_blkp = PREV_FREE_BLKP(ptr);
  int distance = DISTANCE_BETWEEN(next_free_blkp, prev_free_blkp);
  
  if(prev_free_blkp) {
    PUTS(prev_free_blkp, distance);    
  } else { // if ptr was the first block we assign the next block as the beginning of list
    PUTP(ADD_VOIDP(sfl_start, index), next_free_blkp);
  }
  
  if(next_free_blkp) {
    PUTS(PREV_FIELD(next_free_blkp), -distance);
  }
}

static inline void *find_block(size_t size) {
 
  int index = find_index(size); // smallest index that may fit the block
  void *new_block_ptr = GETP(ADD_VOIDP(sfl_start, index)); 
  
  if(new_block_ptr) {
    if(GET_SIZE(HDRP(new_block_ptr)) == size) {    
        remove_from_sfl(new_block_ptr, index);
        return new_block_ptr;
    }
  } else {
    index++;
  }   
  
  for(;index < SFL_SIZE; ++index) {

    new_block_ptr = GETP(ADD_VOIDP(sfl_start, index));
    
    if(!new_block_ptr) { // if there is no blocks in the list continue
      continue;
    }
    
    int min_diff = INT_MAX;    
    void *min_ptr = NULL;

    while(new_block_ptr) {
      int diff = GET_SIZE(HDRP(new_block_ptr)) - size; // diff can be negative !!!
      
      if(diff >= 0 && diff < min_diff) {
        min_diff = diff;
        min_ptr = new_block_ptr;
      }

      new_block_ptr = NEXT_FREE_BLKP(new_block_ptr); 
    }
           
    if(!min_ptr) {
      continue;
    }

    remove_from_sfl(min_ptr, index);
    return min_ptr;
  }

  return NULL;
}

/*
 * add_to_sfl - Add block to segregated free list
 */
static inline void add_to_sfl(void *ptr) {

  assert(GET_ALLOC(HDRP(ptr)) == 0);

  size_t size = GET_SIZE(HDRP(ptr));
  int index = find_index(size);
  void *first_blkp = ADD_VOIDP(sfl_start, index);

  assert((GETP(first_blkp) - ptr) % ALIGNMENT == 0);
  int distance = DISTANCE_BETWEEN(GETP(first_blkp), ptr);

  PUTS(ptr, distance);
  PUTS(PREV_FIELD(ptr), 0);
  
  /* if there is a block in the list assign the pointer ptr to its previous block field */
  if(GETP(first_blkp)) {     
    PUTS(PREV_FIELD(GETP(first_blkp)), -distance);
  }
  PUTP(first_blkp, ptr); // assign ptr as the new first block in list
}

/*
 * split - Split given block if needed; returns size of the possibly split block
 */

static inline size_t split(void *ptr, size_t size) {
  
  size_t ptr_size = GET_SIZE(HDRP(ptr));
  int diff = ptr_size - size;

  if (diff < ALIGNMENT) { // minimal size requirement
    return ptr_size;
  } 

  // splitting
  PUT(HDRP(ptr), PACK(size, 0)); // soon to be allocated block header
  PUT(FTRP(ptr), PACK(size, 0)); // soon to be allocated block footer
  
  remove_from_sfl(ptr, find_index(ptr_size)); 
  // free block
  void *next_block = NEXT_BLKP(ptr);
  PUT(HDRP(next_block), PACK(diff, 0)); // free block header
  PUT(FTRP(next_block), PACK(diff, 0)); // free block footer
  
  add_to_sfl(next_block);
   
  return size;
}

/*
 * coalesce - Possibly coalesce adjecent blocks
 * NOT UPDATED !!! SHOULD REMOVE FROM SEGREGATED FREE LIST IF COALESCED
 * IF COALESCING SHALL BE EVEN DONE AT ALL
 */
/*
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
*/
/*
 * mm_init - Called when a new trace starts.
 */
int mm_init(void) {

  heap_start = mem_sbrk(PSIZE * SFL_SIZE + WSIZE + 3 * WSIZE);
  /* SFL_SIZE is area dedicated for segregated free lists 
   * every entry in the segregated free list array is a pointer to void thus 8 bytes
   * WSIZE is alignment padding
   * 3 * WSIZE is prologue header, prologue footer and epilogue header
   */

  if (heap_start < 0) {
    return -1;
  }

  sfl_start = (void *)heap_start;

  for(int i = 0; i < SFL_SIZE; ++i) {
    PUTP(ADD_VOIDP(sfl_start, i), NULL); 
  }

  heap_start += SFL_SIZE * PSIZE;
  
  /* Alignment padding */
  // TO DO: if SFL_SIZE changes alignment padding is adequately changed too
  PUT(heap_start, 0);    

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

  // size = (size + DSIZE < ALIGNMENT) ? ALIGNMENT : ROUND(size + DSIZE);
  
  void *free_block_ptr = find_block(size);
  
  if(free_block_ptr) { 
    size_t new_size = split(free_block_ptr, size);
  // marking the block as allocated
    PUT(HDRP(free_block_ptr), PACK(new_size, 1));
    PUT(FTRP(free_block_ptr), PACK(new_size, 1));
    return free_block_ptr;
  }
  
  void *new_block = mem_sbrk(size);

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

  // printf("free...\n");
  if (ptr == NULL) {
    return;
  }
  size_t size = GET_SIZE(HDRP(ptr));

  PUT(HDRP(ptr), PACK(size, 0));
  PUT(FTRP(ptr), PACK(size, 0));
  
  // maybe coalescence here?
  add_to_sfl(ptr);
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
  
  static int check_num = -1;
  check_num++; 
  printf("----- checking ----- %d\n", check_num);
  for(int i = 0; i < SFL_SIZE; ++i) {
    
    void *ptr = GETP(ADD_VOIDP(sfl_start, i));
    
    while (ptr) {
      printf("address: %p\n", ptr); 
      printf("size: %d\n", GET_SIZE(HDRP(ptr)));

      ptr = NEXT_FREE_BLKP(ptr);    
    }
  }
}
