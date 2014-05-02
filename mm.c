#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <memory.h>
#include "mm.h"
#include "memlib.h"
#include "assert.h"

team_t team = {
  /* Team name */
  "IKS",
  /* First member's full name */
  "Ian Ker-Seymer",
  /* First member's email address */
  "i.kerseymer@gmail.com",
  /* Second member's full name (leave blank if none) */
  "",
  /* Second member's email address (leave blank if none) */
  ""
};


/////////////////////////////////////////////////////////////////////////////
// Constants and macros
//
// These correspond to the material in Figure 9.43 of the text
// The macros have been turned into C++ inline functions to
// make debugging code easier.
//
/////////////////////////////////////////////////////////////////////////////

#define WSIZE       sizeof(int*)       /* word size (bytes) */
#define DSIZE       sizeof(double)       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */

#define NEXT_PTR(bp) *((void**) bp)
#define SET_PTR(bp, val) ((*(FL_Pointer*)(bp)) = (val) )
#define GETPTR(x) ( *(FL_Pointer *) (x) )

typedef int bool;
#define true  (1)
#define false (0)

static char *heap_listp;  /* pointer to first block */
typedef struct CLNode * FL_Pointer;


struct CLNode {
  struct CLNode *next;
  struct CLNode *prev;
};

//
// Initialize the root of a circular list.
// This has the next & prev pointing to the
// root itself.
//
void CL_init(FL_Pointer root)
{
  root -> next = root;
  root -> prev = root;
}

//
// Add something after "after" in the list. Usually,
// "after" will be the freelist struct
//
void CL_append(FL_Pointer after, FL_Pointer newguy)
{
  newguy -> next = after -> next;
  newguy -> prev = after;
  after -> next = newguy;
  newguy -> next -> prev = newguy;
}

//
// Unlink the element at "ptr". Ptr should NEVER be the
// root / freelist head (the code will still work, but
// you'll have lost all access to the other elements)
//
void CL_unlink(struct CLNode *ptr)
{
  ptr -> prev -> next = ptr -> next;
  ptr -> next -> prev = ptr -> prev;
  ptr -> next = NULL; // be tidy
  ptr -> prev = NULL; // be tidy
}

void CL_print(struct CLNode *root)
{
  struct CLNode *ptr;
  const char *sep = "";
  int count = 0;

  printf("FreeList @ %p: ", root);
  //
  // Note the iteration pattern --- you start with the "next"
  // after the root, and then end when you're back at the root.
  //
  for ( ptr = root -> next; ptr != root; ptr = ptr -> next) {
      count++;
      printf("%s%p", sep, ptr);
      sep = ", ";
    }
  printf(" #%d nodes\n", count);
}


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


struct CLNode free_list;

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
  CL_init(&free_list);

  // Create empty heap
  if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1){
    return -1;
  }

  //alignment padding
  PUT(heap_listp, 0);
  // prologue header
  PUT(heap_listp + (WSIZE), PACK(DSIZE, 1));
  //prologue footer
  PUT(heap_listp + (DSIZE), PACK(DSIZE, 1));
  //epilogue header
  PUT(heap_listp + (3*WSIZE), PACK(0, 1));
  heap_listp += (DSIZE);

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
  FL_Pointer ptr;
  for (ptr = free_list.next; ptr != &free_list; ptr = ptr->next){
    if ( (asize <= GET_SIZE(HDRP(ptr)))) {
      return ptr;
    }
  }

  return NULL;
}

//
// mm_free - Free a block
//
void mm_free(void *bp)
{
  //assert( ! is_on_free_list(bp) );

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
  FL_Pointer prev = PREV_BLKP(bp);
  FL_Pointer next = NEXT_BLKP(bp);

  size_t prev_alloc = GET_ALLOC(FTRP(prev));
  size_t next_alloc = GET_ALLOC(HDRP(next));
  size_t size = GET_SIZE(HDRP(bp));

  //CASE 1 : Both neighbors are allocated
  if (prev_alloc && next_alloc) {
    // we need to add free list node here b/c we do not do it in mm_free
    CL_append(&free_list, bp);
  }

  //CASE 2 : Only next free
  else if (prev_alloc && !next_alloc) {

    // unlink node thats next, b/c our current position will be beggining of new free node
    CL_unlink(next);
    CL_append(&free_list, bp);

    size += GET_SIZE(HDRP(next));
    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));
  }

  //CASE 3 : Only prev free
  else if (!prev_alloc && next_alloc){
    size += GET_SIZE(HDRP(prev));

    // no need to make new here b/c one exists at prev_node
    PUT(FTRP(bp), PACK(size,0));
    PUT(HDRP(prev), PACK(size,0));
    bp = prev;
  }

  //CASE 4 : both neighbors unallocated
  else {
    size += GET_SIZE(HDRP(prev))
      + GET_SIZE(FTRP(next));

    // unlink node that is above us, we can ignore the one below us because that
    // will serve ad the head for this free block
    CL_unlink(next);
    PUT(HDRP(prev), PACK(size,0));
    PUT(FTRP(next), PACK(size,0));
    bp = prev;

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

  // assert( is_on_free_list(bp) );
  place(bp, asize);
  // assert( ! is_on_free_list(bp) );
  return bp;

}

static void place(void *bp, size_t asize)
{
  size_t csize = GET_SIZE(HDRP(bp));


  if ((csize - asize) >= (2*DSIZE)){
    CL_unlink(bp);
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(csize - asize, 0));
    PUT(FTRP(bp), PACK(csize - asize, 0));
    CL_append(&free_list, bp);
  }

  else{
    CL_unlink(bp);
    PUT(HDRP(bp), PACK(csize,1));
    PUT(FTRP(bp), PACK(csize,1));
  }
}

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

