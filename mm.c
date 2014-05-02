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
#include "assert.h"

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
typedef void * FL_Pointer;
#define WSIZE       4       /* word size (bytes) */
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */

#define NEXT_PTR(bp) *((void**) bp)
#define SET_PTR(bp, val) ((*(FL_Pointer*)(bp)) = (val) )
#define GETPTR(x) ( *(FL_Pointer *) (x) )

typedef int bool;
#define true  (1)
#define false (0)
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
  return ((char *)(bp) + GET_SIZE(HDRP(bp)) - 2*WSIZE);
}
static inline void *FREEPTR(void *bp) {
  return ((char *)(bp) + GET_SIZE(HDRP(bp)) - WSIZE);
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

//
// This will add a node to the free list
//
FL_Pointer free_list = NULL;
bool is_on_free_list(void* bp); // decl

void print_list(void *bp) {
  FL_Pointer cursor;
  char *sep = "";
  printf("FL : ");
  for (cursor = free_list; cursor != NULL; cursor = GETPTR(cursor)) {
    printf("%p %s", cursor, sep);
      sep = " -> ";
  }
  printf("\n");
}

static inline void add_to_free_list(void *bp) {
  assert( !is_on_free_list(bp) );
  assert( bp != free_list);
  SET_PTR(bp, free_list);
  free_list = bp;
}

inline void unlink_node(void *bp){
  assert( is_on_free_list(bp) );

  if (free_list == bp){
    //unlink first thing on list
    free_list = GETPTR(bp);
  }else {
    //unlink
    FL_Pointer cursor;
    for (cursor = free_list; GETPTR(cursor) != NULL && GETPTR(cursor) != bp; cursor = GETPTR(cursor)); 
      assert( GETPTR(cursor) == bp);
      SET_PTR(cursor, GETPTR(bp));
    }
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

bool is_on_free_list(void* bp){
  FL_Pointer cursor;
  for (cursor = free_list; cursor != NULL; cursor = GETPTR(cursor)) {
    if( cursor  == bp )
    {
      return true;
    }
  }
  return false;
}

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

  if ((void*)(bp = mem_sbrk(size)) == (void*) -1){
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
  FL_Pointer cursor;

  /*printf("MEMORRY Size: %d\n", GET_SIZE(HDRP(cursor)));*/

  for (cursor = free_list; cursor != NULL; cursor = GETPTR(cursor)){
    if ( (asize <= GET_SIZE(HDRP(cursor)))) {
      printf("find_fit returns %p\n", cursor);
      return cursor;
    }
  }
  //no fit
  printf("NO FIT\n");
  return NULL;
}

//
// mm_free - Free a block
//
void mm_free(void *bp)
{
  assert( ! is_on_free_list(bp) );

  size_t size = GET_SIZE(HDRP(bp));

  PUT(HDRP(bp), PACK(size,0));
  PUT(FTRP(bp), PACK(size,0));
  coalesce(bp);
  //assert( is_on_free_list(bp) );
}

//
// coalesce - boundary tag coalescing. Return ptr to coalesced block
//
static void *coalesce(void *bp)
{
  
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));
  
  //assert( ! is_on_free_list(bp) );


  //CASE 1 : Both neighbors are allocated
  if (prev_alloc && next_alloc) {
    // we need to add free list node here b/c we do not do it in mm_free
    add_to_free_list(bp);
  }

  //CASE 2 : Only next free
  else if (prev_alloc && !next_alloc) {
    // unlink node thats next, b/c our current position will be beggining of new free node

    add_to_free_list(bp);
    unlink_node(NEXT_BLKP(bp));

    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));
  }

  //CASE 3 : Only prev free
  else if (!prev_alloc && next_alloc){
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));

    // no need to make new here b/c one exists at prev_node

    PUT(FTRP(bp), PACK(size,0));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
    bp = PREV_BLKP(bp);
  }

  //CASE 4 : both neighbors unallocated
  else {
    size += GET_SIZE(HDRP(PREV_BLKP(bp)))
      + GET_SIZE(FTRP(NEXT_BLKP(bp)));

    // unlink node that is above us, we can ignore the one below us because that
    // will serve ad the head for this free block

    unlink_node(NEXT_BLKP(bp));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
    bp = PREV_BLKP(bp);
  }

  //assert( is_on_free_list(bp) );

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
//    assert( is_on_free_list(bp) );
    place(bp, asize);
//    assert( ! is_on_free_list(bp) );
    return bp;
  }

  // No fit found. Get more memory and place the block
  extendsize =  MAX(asize, CHUNKSIZE);
  if ((bp = extend_heap(extendsize/WSIZE)) == NULL){
    return NULL;
  }

  assert( is_on_free_list(bp) );
  place(bp, asize);
  printf("malloc finishes with return %p.............\n", bp);
  assert( ! is_on_free_list(bp) );
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
  assert( is_on_free_list(bp) );

  if ((csize - asize) >= (2*DSIZE)){
    unlink_node(bp);
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(csize - asize, 0));
    PUT(FTRP(bp), PACK(csize - asize, 0));
    add_to_free_list(bp);
  }

  else{
    unlink_node(bp);
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

