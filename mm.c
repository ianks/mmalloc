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

#define WSIZE       (sizeof(int*))       /* word size (bytes) */
#define DSIZE       (sizeof(double))       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    16       

#define right_PTR(bp) *((void**) bp)
#define SET_PTR(bp, val) ((*(FL_Pointer*)(bp)) = (val) )
#define GETPTR(x) ( *(FL_Pointer *) (x) )

typedef int bool;
#define true  (1)
#define false (0)

static char *heap_listp;  /* pointer to first block */
typedef struct CLNode * FL_Pointer;


struct CLNode {
  struct CLNode *parent;
  struct CLNode *right;
  struct CLNode *left;
};

//
// Initialize the root of a circular list.
// This has the right & left pointing to the
// root itself.
//
void CL_init(FL_Pointer root)
{
  root -> right = root;
  root -> left = root;
  root -> parent = NULL;
}

//
// Add something after "after" in the list. Usually,
// "after" will be the freelist struct
//
void CL_append(FL_Pointer after, FL_Pointer newguy)
{
  newguy -> right = after -> right;
  newguy -> left = after;
  after -> right = newguy;
  newguy -> right -> left = newguy;
}



//
// Unlink the element at "ptr". Ptr should NEVER be the
// root / freelist head (the code will still work, but
// you'll have lost all access to the other elements)
//
void CL_unlink(struct CLNode *ptr)
{
  ptr -> left -> right = ptr -> right;
  ptr -> right -> left = ptr -> left;
  ptr -> right = NULL; // be tidy
  ptr -> left = NULL; // be tidy
}

void CL_print(struct CLNode *root)
{
  struct CLNode *ptr;
  const char *sep = "";
  int count = 0;

  printf("FreeList @ %p: ", root);
  //
  // Note the iteration pattern --- you start with the "right"
  // after the root, and then end when you're back at the root.
  //
  for ( ptr = root -> right; ptr != root; ptr = ptr -> right) {
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
// Given block ptr bp, compute address of right and leftious blocks
//
static inline void *right_BLKP(void *bp) {
  return  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)));
}

static inline void* left_BLKP(void *bp){
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

void bst_insert(FL_Pointer bp){

  FL_Pointer cursor = &free_list;

  if( bp == &free_list)
    return;


  if (GET_SIZE(cursor) >= GET_SIZE(bp)){
    if (cursor->left == NULL){
      cursor->left = bp;
      bp->parent = cursor;
      return;
    }
    else
      return bst_insert(cursor->left);
  }
  else{
    if (cursor->right == NULL){
      cursor->right = bp;
      bp->parent = cursor;
      return;
    }
    else
      return bst_insert(cursor->right);
  }
}

static inline void bst_remove(FL_Pointer bp){
  //no kidz
  if (bp->right == NULL && bp->left == NULL)
    bp->parent = NULL;

  //one child case 1
  else if (bp->parent != NULL && bp->right != NULL && bp->left == NULL){
    bp->parent->right = bp->right;
    bp->right->parent = bp->parent;
    bp = NULL;
  }
  //one child case 2
  else if (bp->parent != NULL && bp->right == NULL && bp->left != NULL){
    bp->parent->left = bp->left;
    bp->left->parent = bp->parent;
    bp = NULL;
  }
  //two childrenz
  else{

    FL_Pointer tmp;
    // find smallest value in right subtree, goodbye it
    for (tmp = bp->right; tmp != NULL; tmp = tmp->left){
      if (tmp->left == NULL){
        bp = tmp;
        tmp = NULL;
      }
    }
  }
}
  
void *bst_find_fit(size_t asize){
  FL_Pointer cursor = &free_list;

  while(true){
    if (GET_SIZE(HDRP(cursor)) >= asize){
      if (cursor->left == NULL)
        return cursor;
      else
        cursor = cursor->left;
    }
    else{
      if (cursor->right == NULL)
        return cursor;
      else
        cursor = cursor->left;
    }
  }
}
static void *find_fit(size_t asize)
{
  FL_Pointer ptr;
  for (ptr = free_list.right; ptr != &free_list; ptr = ptr->right){
    if ( (asize <= GET_SIZE(HDRP(ptr)))) {
      return ptr;
    }
  }

  return NULL;
}



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
  PUT(HDRP(right_BLKP(bp)), PACK(0,1));
  //Coalesce if leftious block was free

  return coalesce(bp);
}


//
// Practice problem 9.8
//
// find_fit - Find a fit for a block with asize bytes
//


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
  FL_Pointer left = left_BLKP(bp);
  FL_Pointer right = right_BLKP(bp);

  size_t left_alloc = GET_ALLOC(FTRP(left));
  size_t right_alloc = GET_ALLOC(HDRP(right));
  size_t size = GET_SIZE(HDRP(bp));

  //CASE 1 : Both neighbors are allocated
  if (left_alloc && right_alloc) {
    // we need to add free list node here b/c we do not do it in mm_free
    //CL_append(&free_list, bp);
    bst_insert(bp);
  }

  //CASE 2 : Only right free
  else if (left_alloc && !right_alloc) {

    // unlink node thats right, b/c our current position will be beggining of new free node
    //CL_unlink(right);
    //CL_append(&free_list, bp);
    bst_remove(right);
    bst_insert(bp);

    size += GET_SIZE(HDRP(right));
    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));
  }

  //CASE 3 : Only left free
  else if (!left_alloc && right_alloc){
    size += GET_SIZE(HDRP(left));

    // no need to make new here b/c one exists at left_node
    PUT(FTRP(bp), PACK(size,0));
    PUT(HDRP(left), PACK(size,0));
    bp = left;
  }

  //CASE 4 : both neighbors unallocated
  else {
    size += GET_SIZE(HDRP(left))
      + GET_SIZE(FTRP(right));

    // unlink node that is above us, we can ignore the one below us because that
    // will serve ad the head for this free block
    //CL_unlink(right);
    bst_remove(right);
    PUT(HDRP(left), PACK(size,0));
    PUT(FTRP(right), PACK(size,0));
    bp = left;

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
  if ((bp = bst_find_fit(asize)) != NULL){
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


  if ((csize - asize) >= (3*DSIZE)){
    //CL_unlink(bp);
    bst_remove(bp);
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    bp = right_BLKP(bp);
    PUT(HDRP(bp), PACK(csize - asize, 0));
    PUT(FTRP(bp), PACK(csize - asize, 0));
    //CL_append(&free_list, bp);
    bst_insert(bp);
  }

  else{
    //CL_unlink(bp);
    bst_remove(bp);
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

  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = right_BLKP(bp)) {
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

