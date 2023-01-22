/*
 * Ziemowit Bączewski 324331
 * I am the sole author of this source code.
 * Some of the macros are taken from CSAPP book.
 * I tried following the notation presented in the book.
 */
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
#define WSIZE 4              /* Word size*/
#define DSIZE 8              /* Double word size*/
#define PSIZE 8              /* Size of pointer in bytes */
#define CHUNK_SIZE (1 << 12) /* Size of memory chunk*/

/* Pack size, allocated bit and previous free bit into a word */
#define PACK(size, alloc, pfree) ((size) | (alloc) | (pfree))

/* calulate distance between two pointers with one unit being equal to
 * ALIGNMENT*/
#define DISTANCE_BETWEEN(p1, p2) ((p1 && p2) ? (p1 - p2) / ALIGNMENT : 0)

/* Read a word at address p */
#define GET(p) (*(unsigned int *)(p)) // read unsigned integer value
#define GETS(p) (*(int *)(p))         // read signed integer value
#define GETP(p) (*(void **)(p))       // read a pointer

/* Write a word at addres p */
#define PUT(p, val)                                                            \
  (*(unsigned int *)(p) = (val))               // write unsigned integer value
#define PUTS(p, val) (*(int *)(p) = (val))     // write signed integer value
#define PUTP(p, pval) (*(void **)(p) = (pval)) // write a pointer

/* Read the size, allocated and previous free fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_PFREE(p) (GET(p) & 0x2)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of its previous free block field */
#define PREV_FIELD(bp) ((char *)(bp) + WSIZE)

/* Given block ptr bp, read pointers to the next free block in segregated free
 * list */
#define NEXT_FREE_BLKP(bp)                                                     \
  (GETS(bp) ? (void *)((char *)(bp) + GETS(bp) * ALIGNMENT) : NULL)
#define PREV_FREE_BLKP(bp)                                                     \
  (GETS(PREV_FIELD(bp))                                                        \
     ? (void *)((char *)(bp) + GETS(PREV_FIELD(bp)) * ALIGNMENT)               \
     : NULL)

/* Add n * PSIZE bytes to void pointer since void pointer arthimetic is illegal
 * and sizeof(void *) = PSIZE */
#define ADD_VOIDP(p, n) ((void *)((char *)(p) + PSIZE * n))

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp)                                                          \
  ((char *)(bp)-GET_SIZE(                                                      \
    ((char *)(bp)-DSIZE))) // only to be used when it is known that the previous
                           // block is free

/* Round size to ALIGNMENT */
#define ROUND(size) ((size + ALIGNMENT - 1) & -ALIGNMENT)
/* Round size to CHUNK_SIZE */
#define ROUND_MEM(size) ((size + CHUNK_SIZE - 1) & -CHUNK_SIZE)

#define SINGULAR_BLOCKS_NUM                                                    \
  16 // Number of free lists with blocks of its own sizes
#define RANGED_BLOCKS_NUM                                                      \
  8 // Number of free lists with blocks in a size classes

/* Number of all free lists */
#define SFL_SIZE (SINGULAR_BLOCKS_NUM + RANGED_BLOCKS_NUM)

/* Number of leading zeros defining limits of size classes in segregated free
 * lists */
#define LOWEST_LEADING_ZEROS __builtin_clz(256)    // 23 in 32 bit int
#define HIGHEST_LEADING_ZEROS __builtin_clz(32768) // 16 in 32 bit int

static char *heap_start;    /* Address of the prologue footer */
static char *epilogue_blkp; /* Points at epilogue header */
static void *sfl_start;     /* Adress of first list in segregated free lists*/

/*
 * Memory allocator utilizes segregated free lists.
 * free blocks ranging in size from 16 to 256 bytes are put into their own lists
and the rest is put into power of two size classes.
 *
 * Headers and footers store information about size and allocation of the block
and whether the previous block is free.
 * Headers and footers are unsigned integers and take 4 bytes.
 *
 * Allocated blocks only have headers.
 * Free blocks have headers footers and store information
 * about the next and previous free blocks in the list
 *
 * The next free block and previous free block field are signed integers and
 * indicate the distance between the blocks with one unit being equal to
ALIGNMENT.
 *
 *  Free block structure:
 *
 *  |============================================|
 *  |        | NEXT  | PREVIOUS |       |        |
 *  | HEADER | FREE  | FREE     |  ...  | FOOTER |
 *  |        | BLOCK | BLOCK    |       |        |
 *  |============================================|
 *
 *  Allocated block structure:
 *
 *  |==================|
 *  |        |         |
 *  | HEADER | PAYLOAD |
 *  |        |         |
 *  |==================|
 *
 *
 *  Memory allocation:
 *  First, algorithm tries to find a sufficiently sized block with find_block()
function. If it finds a good block it splits it if needed and returns pointer to
the block of desired size. If a free block of asked size or larger is not found
in the segregated free list, heap is increased by CHUNK_SIZE. Then the chunk is
split if needed and pointer to a block of requested size is returned. If a block
was split, the free part is added to the segregated free list.
 *
 *  Freeing memory:
 *  Freeing is straightforward. Block is marked as free in header and footer is
added. Previous block field is changed in the next block. The newly freed block
is then coalesced with adjoining blocks if possible. Finally, the block is added
to the segregated free lists.
 *
 */

/*
 * find_index - depending on size find index of list that stores blocks of that size
 * It utilizes the count leading zeros function to determine which range given size falls into.
 */

static inline int find_index(size_t size) {

  if (size <= SINGULAR_BLOCKS_NUM * ALIGNMENT) {
    return (size / ALIGNMENT) - 1;
  }

  int leading_zeros = __builtin_clz(size);

  if (leading_zeros <= HIGHEST_LEADING_ZEROS) {
    return SFL_SIZE - 1;
  }

  return LOWEST_LEADING_ZEROS - leading_zeros + SINGULAR_BLOCKS_NUM;
}

/*
 * add_to_sfl - Add block to segregated free list
 */
static inline void add_to_sfl(void *ptr) {

  size_t size = GET_SIZE(HDRP(ptr));
  int index = find_index(size);
  void *first_blkp = ADD_VOIDP(sfl_start, index);

  int distance = DISTANCE_BETWEEN(GETP(first_blkp), ptr);

  PUTS(ptr, distance);
  PUTS(PREV_FIELD(ptr), 0);

  /* if there is a block in the list assign the pointer ptr to its previous
   * block field */
  if (GETP(first_blkp)) {
    PUTS(PREV_FIELD(GETP(first_blkp)), -distance);
  }
  PUTP(first_blkp, ptr); // assign ptr as the new first block in list
}

/*
 * remove_from_sfl - Remove block from segregated free list
 * Index to the segregated free list can be passed.
 */
static inline void remove_from_sfl(void *ptr, int index) {

  if (ptr == NULL) {
    return;
  }

  void *next_free_blkp = NEXT_FREE_BLKP(ptr);
  void *prev_free_blkp = PREV_FREE_BLKP(ptr);
  int distance = DISTANCE_BETWEEN(next_free_blkp, prev_free_blkp);

  if (prev_free_blkp) {
    PUTS(prev_free_blkp, distance);
  } else { // if ptr was the first block we assign the next block as the
           // beginning of list
    if (index < 0) {
      index = find_index(GET_SIZE(HDRP(ptr)));
    }

    PUTP(ADD_VOIDP(sfl_start, index), next_free_blkp);
  }

  if (next_free_blkp) {
    PUTS(PREV_FIELD(next_free_blkp), -distance);
  }
}

/*
 * find_block - Find a block with enough size.
 * If the size is smaller or equal than SINGULAR_BLOCKS_NUM * ALIGNMENT then it just returns the first block in the list. 
 * Else it tries to find the best fit for the block in the list determined by find_size function.
 */

static inline void *find_block(size_t size) {

  int index = find_index(size); // smallest index that may fit the block
  void *new_block_ptr = GETP(ADD_VOIDP(sfl_start, index));

  if (new_block_ptr) {
    if (GET_SIZE(HDRP(new_block_ptr)) == size) {
      return new_block_ptr;
    }
  } else {
    index++;
  }

  for (; index < SFL_SIZE; ++index) {

    new_block_ptr = GETP(ADD_VOIDP(sfl_start, index));

    if (!new_block_ptr) { // if there is no blocks in the list continue
      continue;
    }

    int min_diff = INT_MAX;
    void *min_ptr = NULL;

    while (new_block_ptr) {
      int diff = GET_SIZE(HDRP(new_block_ptr)) - size; // diff can be negative

      if (diff > 0 && diff < min_diff) {
        min_diff = diff;
        min_ptr = new_block_ptr;

      } else if (diff == 0) { // if block has perfect size return it
        return new_block_ptr;
      }

      new_block_ptr = NEXT_FREE_BLKP(new_block_ptr);
    }

    /* if none of the blocks in the list are sufficient size, continue */
    if (!min_ptr) {
      continue;
    }

    return min_ptr;
  }

  return NULL;
}

/*
 * split - Split given block if needed; returns pointer to the free block of desired size. 
 * It does the splitting abnormally so that the first block is the one to remain free and the second is the one to which the pointer is returned.
 */
static inline void *split(void *ptr, size_t size) {

  size_t ptr_size = GET_SIZE(HDRP(ptr));
  int diff = ptr_size - size;

  if (diff < ALIGNMENT) { // minimal size requirement
    return ptr;
  } else if (size == 0) {
    return ptr;
  }

  size_t pfree = GET_PFREE(HDRP(ptr));

  // free block
  PUT(HDRP(ptr), PACK(diff, 0, pfree));
  PUT(FTRP(ptr), PACK(diff, 0, pfree));

  // soon to be allocated block
  void *next_blkp = NEXT_BLKP(ptr);
  PUT(HDRP(next_blkp), PACK(size, 0, 2));
  PUT(FTRP(next_blkp), PACK(size, 0, 2));

  return next_blkp;
}

/*
 * coalesce_front - Possibly coalesce the block in the front
 */
static void *coalesce_front(void *ptr) {

  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
  size_t size = GET_SIZE(HDRP(ptr));

  if (!next_alloc) { // next block is free

    void *next_blkp = NEXT_BLKP(ptr);
    size_t next_size = GET_SIZE(HDRP(next_blkp));

    remove_from_sfl(next_blkp, -1);

    size += next_size;

    size_t pfree = GET_PFREE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0, pfree));
    PUT(FTRP(next_blkp), PACK(size, 0, pfree));
  }

  return ptr;
}

/*
 * coalesce_back - Possibly coalesce the block in the back.
 */
static void *coalesce_back(void *ptr) {

  size_t prev_alloc = !GET_PFREE(HDRP(ptr));
  size_t size = GET_SIZE(HDRP(ptr));

  if (!prev_alloc) {

    void *prev_blkp = PREV_BLKP(ptr);
    size_t prev_size = GET_SIZE(HDRP(prev_blkp));

    remove_from_sfl(prev_blkp, -1);

    size += prev_size;

    size_t pfree = GET_PFREE(HDRP(prev_blkp));

    PUT(HDRP(prev_blkp), PACK(size, 0, pfree));
    PUT(FTRP(ptr), PACK(size, 0, pfree));

    return prev_blkp;
  }

  return ptr;
}

/*
 * mm_init - Called when a new trace starts.
 */
int mm_init(void) {

  heap_start = mem_sbrk(PSIZE * SFL_SIZE + WSIZE + 3 * WSIZE);

  /* SFL_SIZE is number of segregated free lists.
   * PSIZE * SFL_SIZE for segregated free lists array
   * WSIZE for alignment padding
   * 3 * WSIZE for prologue header, prologue footer and epilogue header
   */

  if (heap_start < 0) {
    return -1;
  }

  sfl_start = (void *)heap_start;

  /* Segregated free lists array */
  for (int i = 0; i < SFL_SIZE; ++i) {
    PUTP(ADD_VOIDP(sfl_start, i), NULL);
  }

  heap_start += SFL_SIZE * PSIZE;

  /* Alignment padding */
  PUT(heap_start, 0);

  PUT(heap_start + (1 * WSIZE), PACK(WSIZE, 1, 0)); /* Prologue header */
  PUT(heap_start + (2 * WSIZE), PACK(WSIZE, 1, 0)); /* Prologue footer */
  PUT(heap_start + (3 * WSIZE), PACK(0, 1, 0));     /* Epilogue header */
  heap_start += (2 * WSIZE);
  epilogue_blkp = heap_start + WSIZE;
  PUT(epilogue_blkp, PACK(0, 1, 0));

  return 0;
}

/*
 * malloc - Allocate a block by finding a free one in segregated free lists or
 * by allocating a chunk of size CHUNK_SIZE and then splitting it if necessary.
 * Always allocate a block which size is a multiple of ALIGNMENT
 */
void *malloc(size_t size) {

  size = (size + WSIZE < ALIGNMENT) ? ALIGNMENT : ROUND(size + WSIZE);

  void *free_blkp = find_block(size);

  /* free block in the sfl is found */
  if (free_blkp) {

    size_t old_size = GET_SIZE(HDRP(free_blkp));
    void *split_blkp = split(free_blkp, size);
    int old_size_index = find_index(old_size);

    /* remove the block from sfl if the found block is perfect size or when
     * splitting the block resulted in moving it to another size class */
    if (split_blkp == free_blkp ||
        (find_index(old_size - size) != old_size_index)) {
      remove_from_sfl(free_blkp, old_size_index);

      /* add split block back to sfl */
      if (split_blkp != free_blkp) {
        add_to_sfl(free_blkp);
      }
    }

    /* marking the block as allocated */
    PUT(HDRP(split_blkp), PACK(size, 1, GET_PFREE(HDRP(split_blkp))));

    void *next_blkh = HDRP(NEXT_BLKP(split_blkp));
    PUT(next_blkh, PACK(GET_SIZE(next_blkh), GET_ALLOC(next_blkh), 0));
    return split_blkp;
  }

  /* Suitable block was not found in the segregated free lists so increasing the heap */
  size_t mem_incr = ROUND_MEM(size);
  free_blkp = mem_sbrk(mem_incr);

  size_t pfree = GET_PFREE(epilogue_blkp);

  PUT(HDRP(free_blkp), PACK(mem_incr, 0, pfree));

  void *split_blkp = split(free_blkp, size);
  
  /* If block was split add the remaining part to the sfl */
  if (split_blkp != free_blkp) {
    add_to_sfl(free_blkp);
    PUT(HDRP(split_blkp), PACK(size, 1, 2));
  } else {
    PUT(HDRP(split_blkp), PACK(size, 1, pfree));
  }

  /* Move epilogue header */
  epilogue_blkp += mem_incr;
  PUT(epilogue_blkp, PACK(0, 1, 0)); // new epilogue header

  return split_blkp;
}

/*
 * free - Free a block, coalesce if possible and add it to segregated free list
 */
void free(void *ptr) {

  if (ptr == NULL) {
    return;
  }

  size_t size = GET_SIZE(HDRP(ptr));
  size_t pfree = GET_PFREE(HDRP(ptr));

  PUT(HDRP(ptr), PACK(size, 0, pfree));
  PUT(FTRP(ptr), PACK(size, 0, pfree));

  void *next_blkh = HDRP(NEXT_BLKP(ptr));
  /* switching previous free bit in the next block */
  PUT(next_blkh, PACK(GET_SIZE(next_blkh), GET_ALLOC(next_blkh), 2));

  coalesce_front(ptr);
  ptr = coalesce_back(ptr);
  add_to_sfl(ptr);
}

/*
 * realloc - Change the size of the block by coalescing block in the front
 * or by calling malloc and copying the data.
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

  size_t old_size = GET_SIZE(HDRP(old_ptr));
  size_t r_size = ROUND(size + WSIZE);

  /* If the requested size is smaller or equal than the currently allocated */
  if (old_size == r_size) {
    return old_ptr;
  } else if (old_size > r_size) {

    PUT(HDRP(old_ptr), PACK(r_size, 1, GET_PFREE(HDRP(old_ptr))));

    void *next_blkp = NEXT_BLKP(old_ptr);
    PUT(HDRP(next_blkp), PACK(old_size - r_size, 0, 0));
    PUT(FTRP(next_blkp), PACK(old_size - r_size, 0, 0));

    add_to_sfl(next_blkp);

    return old_ptr;
  }

  void *next_blkp = NEXT_BLKP(old_ptr);
  size_t next_blk_size = GET_SIZE(HDRP(next_blkp));

  /* If the next block is free and sufficient size, coalesce current and next
   * block. It also splits the next block if it's too big.
   */
  if (!GET_ALLOC(HDRP(next_blkp)) && next_blk_size + old_size >= r_size) {

    remove_from_sfl(next_blkp, -1);
    void *split_blkp = split(next_blkp, next_blk_size + old_size - r_size);

    if (split_blkp != next_blkp) {
      add_to_sfl(split_blkp);
      PUT(HDRP(split_blkp), PACK(GET_SIZE(HDRP(split_blkp)), 0, 0));
      PUT(FTRP(split_blkp), PACK(GET_SIZE(HDRP(split_blkp)), 0, 0));
    } else {
      next_blkp = NEXT_BLKP(next_blkp);

      size_t next_alloc = GET_ALLOC(HDRP(next_blkp));

      PUT(HDRP(next_blkp), PACK(GET_SIZE(HDRP(next_blkp)), next_alloc, 0));
      if (!next_alloc) {
        PUT(FTRP(next_blkp), PACK(GET_SIZE(HDRP(next_blkp)), next_alloc, 0));
      }
    }

    coalesce_front(old_ptr);

    PUT(HDRP(old_ptr), PACK(r_size, 1, GET_PFREE(HDRP(old_ptr))));

    return old_ptr;
  }

  void *new_ptr = malloc(size);

  /* If malloc() fails, the original block is left untouched. */
  if (!new_ptr)
    return NULL;

  /* copy the data */
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
 * mm_checkheap - Just some debugging information
 */
void mm_checkheap(int verbose) {

  static int check_num = 0;
  check_num++;
  printf("----- checking ----- %d\n", check_num);

  char *blk_check = heap_start + DSIZE;
  int blk_num = 0;

  if (verbose > 0) {
    printf("Heap start offset: %p\n", heap_start + WSIZE);

    while (blk_check < epilogue_blkp) {

      printf("block number: %d size: %u ", blk_num, GET_SIZE(HDRP(blk_check)));
      printf("alloc: %d pfree: %d address: %p\n", GET_ALLOC(HDRP(blk_check)),
             GET_PFREE(HDRP(blk_check)), blk_check);
      blk_num++;
      blk_check = NEXT_BLKP(blk_check);
    }

    printf("Epilogue header: %p alloc: %d pfree: %d\n", epilogue_blkp,
           GET_ALLOC(epilogue_blkp), GET_PFREE(epilogue_blkp));
  }

  if (verbose > 1) { // checking the segregated fit lists

    printf("--- Segregated free lists ---\n");

    for (int i = 0; i < SFL_SIZE; ++i) {

      void *ptr = GETP(ADD_VOIDP(sfl_start, i));

      while (ptr) {
        printf("address: %p\n", ptr);
        printf("size: %d\n", GET_SIZE(HDRP(ptr)));

        ptr = NEXT_FREE_BLKP(ptr);
      }
    }
  }
}
