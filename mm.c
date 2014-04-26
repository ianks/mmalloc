/*
 * mm-implicit.c -  Simple allocator based on implicit free lists,
 *                  first fit placement, and boundary tag coalescing.
 *
 * Each block has header and footer of the form:
 *
 *      31                     3  2  1  0
 *      -----------------------------------
 *     | s  s  s  s  ... s  s  s  0  0  a/f
 *      -----------------------------------
 *
 * where s are the meaningful size bits and a/f is set
 * iff the block is allocated. The list has the following form:
 *
 * begin                                                          end
 * heap                                                           heap
 *  -----------------------------------------------------------------
 * |  pad   | hdr(8:a) | ftr(8:a) | zero or more usr blks | hdr(8:a) |
 *  -----------------------------------------------------------------
 *          |       prologue      |                       | epilogue |
 *          |         block       |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 */
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <memory.h>
#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
  /* Team name */
  "Awesome to the MAX",
  /* First member's full name */
  "Ian Ker-Seymer",
  /* First member's email address */
  "i.kerseymer@gmail.com",
  /* Second member's full name (leave blank if none) */
  "Brandon Mikulka",
  /* Second member's email address (leave blank if none) */
  "brandon.mikulka@colorado.edu"
};

/////////////////////////////////////////////////////////////////////////////
// Constants and macros
//
// These correspond to the material in Figure 9.43 of the text
// The macros have been turned into C++ inline functions to
// make debugging code easier.
//
/////////////////////////////////////////////////////////////////////////////
#define WSIZE       4       /* word size (bytes) */
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */

static inline int MAX(int x, int y) {
  return x > y ? x : y;
}

//
// Pack a size and allocated bit into a word
// We mask of the "alloc" field to insure only
// the lower bit is used
//
static inline size_t PACK(size_t size, int alloc) {
  return ((size) | (alloc & 0x1));
}

//
// Read and write a word at address p
//
static inline size_t GET(void *p) { return  *(size_t *)p; }
static inline void PUT( void *p, size_t val)
{
  *((size_t *)p) = val;
}

//
// Read the size and allocated fields from address p
//
static inline size_t GET_SIZE( void *p )  {
  return GET(p) & ~0x7;
}

static inline int GET_ALLOC( void *p  ) {
  return GET(p) & 0x1;
}

//
// Given block ptr bp, compute address of its header and footer
//
static inline void *HDRP(void *bp) {

  return ( (char *)bp) - WSIZE;
}
static inline void *FTRP(void *bp) {
  return ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE);
}

//
// Given block ptr bp, compute address of next and previous blocks
//
static inline void *NEXT_BLKP(void *bp) {
  return  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)));
}

static inline void* PREV_BLKP(void *bp){
  return  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)));
}

/////////////////////////////////////////////////////////////////////////////
//
// Global Variables
//

static char *heap_listp;  /* pointer to first block */

//
// function prototypes for internal helper routines
//
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp);
static void checkblock(void *bp);

//
// mm_init - Initialize the memory manager
//
int mm_init(void)
{

  // Create empty heap
  if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1){
    return -1;
  }
  //alignment padding
  PUT(heap_listp, 0);
  // prologue header
  PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
  //prologue footer
  PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
  //epilogue header
  PUT(heap_listp + (3*WSIZE), PACK(0, 1));
  heap_listp += (2*WSIZE);

  //extend empty heap with free block of CHUNKSIZE byes
  if (extend_heap(CHUNKSIZE/WSIZE) == NULL){
    return -1;
  }
  return 0;
}


//
// extend_heap - Extend heap with free block and return its block pointer
//
static void *extend_heap(size_t words)
{
  char *bp;
  size_t size;

  //Allocate even number of words to maintain alignment
  size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;

  if ((long)(bp = mem_sbrk(size)) == -1){
    return NULL;
  }

  //Initialize free block header/footer and epilogue header
  //free block header
  PUT(HDRP(bp), PACK(size,0));
  //free block footer
  PUT(FTRP(bp), PACK(size,0));
  //new epilogue header
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));

  //Coalesce if previous block was free
  return coalesce(bp);
}


//
// Practice problem 9.8
//
// find_fit - Find a fit for a block with asize bytes
//
static void *find_fit(size_t asize)
{
  // first fit search
  void *bp;

  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
    if ( !GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
        return bp;
    }
  }
  //no fit
  return NULL;
}

//
// mm_free - Free a block
//
void mm_free(void *bp)
{

  size_t size = GET_SIZE(HDRP(bp));

  PUT(HDRP(bp), PACK(size,0));
  PUT(FTRP(bp), PACK(size,0));
  coalesce(bp);
}

//
// coalesce - boundary tag coalescing. Return ptr to coalesced block
//
static void *coalesce(void *bp)
{
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));

  //CASE 1 : Neither neighbor is unallocated
  if (prev_alloc && next_alloc) {
    return bp;
  }

  //CASE 2 : Only next unallocated
  else if (prev_alloc && !next_alloc) {
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));
  }

  //CASE 3 : Only prev unallocated
  else if (!prev_alloc && next_alloc){
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(PREV_BLKP(bp)), PACK(size,0));
    bp = PREV_BLKP(bp);
  }

  //CASE 4 : both neighbors unallocated
  else {
    size += GET_SIZE(HDRP(PREV_BLKP(bp)))
          + GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
    bp = PREV_BLKP(bp);
  }

  return bp;
}

//
// mm_malloc - Allocate a block with at least size bytes of payload
//
void *mm_malloc(size_t size)
{
  //adjusted block size
  size_t asize;
  //ammount to extend heap if the new block doesnt fit
  size_t extendsize;
  char *bp;

  //ignore spurious requests
  if (size == 0){
    return NULL;
  }

  //adjust block size to include overhead and alignment reqs
  if (size <= DSIZE){
    asize = 2*DSIZE;
  }
  else{
    //round size up to nearest mult of DSIZE then add DSIZE
    asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
  }

  //search the free list for a fit
  if ((bp = find_fit(asize)) != NULL){
    place(bp, asize);
    return bp;
  }

  // No fit found. Get more memory and place the block
  extendsize =  MAX(asize, CHUNKSIZE);
  if ((bp = extend_heap(extendsize/WSIZE)) == NULL){
    return NULL;
  }
  place(bp, asize);
  return bp;




}

//
//
// Practice problem 9.9
//
// place - Place block of asize bytes at start of free block bp
//         and split if remainder would be at least minimum block size
//
static void place(void *bp, size_t asize)
{
  size_t csize = GET_SIZE(HDRP(bp));

  if ((csize - asize) >= (2*DSIZE)){
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(csize - asize, 0));
    PUT(FTRP(bp), PACK(csize - asize, 0));
  }

  else{
    PUT(HDRP(bp), PACK(csize,1));
    PUT(FTRP(bp), PACK(csize,1));
  }
}

//
// mm_realloc -- implemented for you
//
void *mm_realloc(void *ptr, size_t size)
{
  void *newp;
  size_t copySize;

  newp = mm_malloc(size);
  if (newp == NULL) {
    printf("ERROR: mm_malloc failed in mm_realloc\n");
    exit(1);
  }
  copySize = GET_SIZE(HDRP(ptr));
  if (size < copySize) {
    copySize = size;
  }
  memcpy(newp, ptr, copySize);
  mm_free(ptr);
  return newp;
}

//
// mm_checkheap - Check the heap for consistency
//
void mm_checkheap(int verbose)
{
  //
  // This provided implementation assumes you're using the structure
  // of the sample solution in the text. If not, omit this code
  // and provide your own mm_checkheap
  //
  void *bp = heap_listp;

  if (verbose) {
    printf("Heap (%p):\n", heap_listp);
  }

  if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp))) {
	printf("Bad prologue header\n");
  }
  checkblock(heap_listp);

  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    if (verbose)  {
      printblock(bp);
    }
    checkblock(bp);
  }

  if (verbose) {
    printblock(bp);
  }

  if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp)))) {
    printf("Bad epilogue header\n");
  }
}

static void printblock(void *bp)
{
  size_t hsize, halloc, fsize, falloc;

  hsize = GET_SIZE(HDRP(bp));
  halloc = GET_ALLOC(HDRP(bp));
  fsize = GET_SIZE(FTRP(bp));
  falloc = GET_ALLOC(FTRP(bp));

  if (hsize == 0) {
    printf("%p: EOL\n", bp);
    return;
  }

  printf("%p: header: [%d:%c] footer: [%d:%c]\n",
	 bp,
	 (int) hsize, (halloc ? 'a' : 'f'),
	 (int) fsize, (falloc ? 'a' : 'f'));
}

static void checkblock(void *bp)
{
  if ((size_t)bp % 8) {
    printf("Error: %p is not doubleword aligned\n", bp);
  }
  if (GET(HDRP(bp)) != GET(FTRP(bp))) {
    printf("Error: header does not match footer\n");
  }
}

