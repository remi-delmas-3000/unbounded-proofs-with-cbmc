/* list append verification using the abstract objects program transformation */
#include "list.h"
#include "../pointer_predicates.h"
#include "lseg.h"
#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

// The semantics of lseg(x, A, y) is given in terms of abstract objects and
// points-to sets
// PT(x) = {&A}
// PT(A.next) = {&A} union PT(y)

// PT(x) = {&A1};
// PT(x->next) = {&A1, null}
// PT(y) = {&A2};
// PT(tail) = {}
// PT(tail->next) = {}
// PT(old_x) = {}
// PT(old_tail) = {}
// PT(A1.next) = {&A1, null};
// PT(A2.next) = {&A2, null};
// conditional assigns clause
// (A1.next == NULL): A1.next

void list_append_base(list_t *x,list_t *y)
// requires lseg(x, null)
// requires lseg(y, null)
// ensures lseg(y, null)
// ensures lseg(x, y)
{
  // PT(x) = {&A1}
  // PT(x->next) = {&A1, null}
  // PT(y) = {&A2}
  // PT(tail) = {}
  // PT(tail->next) = {}
  // PT(old_x) = {}
  // PT(old_tail) = {}
  // PT(A1.next) = {&A1, null}
  // PT(A2.next) = {&A2, null}
  // |A1| = 3
  // |A2| = 2
  if (x->next == NULL) {
    // PT(x) = {&A1}
    // PT(x->next) = {null}
    // PT(y) = {&A2}
    // PT(tail) = {}
    // PT(tail->next) = {}
    // PT(old_x) = {}
    // PT(old_tail) = {}
    // PT(A1.next) = {null}
    // PT(A2.next) = {&A2, null}
    // |A1| = 1
    // |A2| = 2
    x->next = y;
    // PT(x) = {&A1}
    // PT(x->next) = {&A2}
    // PT(y) = {&A2}
    // PT(tail) = {}
    // PT(tail->next) = {}
    // PT(old_x) = {}
    // PT(old_tail) = {}
    // PT(A1.next) = {&A2}
    // PT(A2.next) = {&A2, null}
    // |A1| = 1
    // |A2| = 4
    return;
  }
  // PT(x) = {&A1}
  // PT(x->next) = {&A1}
  // PT(y) = {&A2}
  // PT(tail) = {}
  // PT(tail->next) = {}
  // PT(old_x) = {}
  // PT(old_tail) = {}
  // PT(A1.next) = {&A1};
  // PT(A2.next) = {&A2, null};
  // |A1| = 3
  // |A2| = 2

  list_t *tail = x->next;
  list_t *old_x = x;

  // PT(x) = {&A1}
  // PT(x->next) = {&A1}
  // PT(y) = {&A2}
  // PT(tail) = {&A1}
  // PT(tail->next) = {&A1, null}
  // PT(old_x) = {&A1}
  // PT(old_tail) = {}
  // PT(A1.next) = {&A1};
  // PT(A2.next) = {&A2, null};
  // |A1| = 6
  // |A2| = 2

  while (tail->next != NULL)
  // fixpoint
  // PT(x) = {&A1}
  // PT(x->next) = {&A1}
  // PT(y) = {&A2}
  // PT(tail) = {&A1}
  // PT(tail->next) = {&A1}
  // PT(old_x) = {&A1}
  // PT(old_tail) = {&A1}
  // PT(A1.next) = {&A1};
  // PT(A2.next) = {&A2, null};
  // |A1| = 7
  // |A2| = 2

  // assigns tail
  // loop invariant lseg(x, tail) && lseg(tail, NULL)
  {

    list_t *old_tail = tail;
    tail = tail->next;
    // fixpoint
    // PT(x) = {&A1}
    // PT(x->next) = {&A1}
    // PT(y) = {&A2}
    // PT(tail) = {&A1}
    // PT(tail->next) = {&A1, null}
    // PT(old_x) = {&A1}
    // PT(old_tail) = {&A1}
    // PT(A1.next) = {&A1};
    // PT(A2.next) = {&A2, null};
    // |A1| = 7
    // |A2| = 2
  }
  // post loop
  // PT(x) = {&A1}
  // PT(x->next) = {&A1}
  // PT(y) = {&A2}
  // PT(tail) = {&A1}
  // PT(tail->next) = {null}
  // PT(old_x) = {&A1}
  // PT(old_tail) = {&A1}
  // PT(A1.next) = {&A1};
  // PT(A2.next) = {&A2, null};
  // |A1| = 6
  // |A2| = 2
  tail->next = y;
  // PT(x) = {&A1}
  // PT(x->next) = {&A1}
  // PT(y) = {&A2}
  // PT(tail) = {&A1}
  // PT(tail->next) = {&A2}
  // PT(old_x) = {&A1}
  // PT(old_tail) = {&A1}
  // PT(A1.next) = {&A1};
  // PT(A2.next) = {&A2, null};
  // |A1| = 6
  // |A2| = 2
  assert(x == old_x); // must pass
  assert(x != old_x); // must fail
}


// concretisation of A1
list_t a11;
list_t a12;
list_t a13;
list_t a14;
list_t a15;
list_t a16;
list_t a17;
#define SIZE_A1 7
#define SEL_A1                                                                 \
  (nondet_bool()   ? &a11                                                      \
   : nondet_bool() ? &a12                                                      \
   : nondet_bool() ? &a13                                                      \
   : nondet_bool() ? &a14                                                      \
   : nondet_bool() ? &a15                                                      \
   : nondet_bool() ? &a16                                                      \
                   : &a17)
#define INC_A1(X)                                                              \
  ((X == &a11) || (X == &a12) || (X == &a13) || (X == &a14) || (X == &a15) ||  \
   (X == &a16) || (X == &a17))

// concretisation of A2
list_t a21;
list_t a22;
list_t a23;
list_t a24;
#define SIZE_A2 4
#define SEL_A2                                                                 \
  (nondet_bool() ? &a21 : nondet_bool() ? &a22 : nondet_bool() ? &a23 : &a24)
#define INC_A2(X) ((X == &a21) || (X == &a22) || (X == &a23) || (X == &a24))


// transformed program
void list_append(list_t *x, list_t *y) {
  if (x->next == NULL) {
    x->next = y;
    return;
  }

  list_t *tail = x->next;
  list_t *old_x = x;

  // check base case lseg(tail, A1, null)
  {
    list_t *current = tail;
    size_t i = 0;
    bool ok = true;
    while(i < SIZE_A1) {
      if(current == NULL) {
        break;
      }
      if(!INC_A1(current)) {
        ok = false;
        break;
      }
      current = current->next;
      i++;
    }
    assert(ok);
  }

  // check base case lseg(x, A1, tail)
  {
    list_t *current = x;
    size_t i = 0;
    bool ok = true;
    while(i < SIZE_A1) {
      if(current == tail) {
        break;
      }
      if(!INC_A1(current)) {
        ok = false;
        break;
      }
      current = current->next;
      i++;
    }
    assert(ok);
  }

  // loopback tail
  tail = nondet_bool() ? SEL_A1 : tail;

  // assume step case lseg(tail, A1, null)
  {
    list_t *current = tail;
    size_t i = 0;
    bool ok = true;
    while(i < SIZE_A1) {
      if(current == NULL) {
        break;
      }
      if(!INC_A1(current)) {
        ok = false;
        break;
      }
      current = current->next;
      i++;
    }
    __CPROVER_assume(ok);
  }

  // assume step case lseg(x, A1, tail)
  {
    list_t *current = x;
    size_t i = 0;
    bool ok = true;
    while(i < SIZE_A1) {
      if(current == tail) {
        break;
      }
      if(!INC_A1(current)) {
        ok = false;
        break;
      }
      current = current->next;
      i++;
    }
    __CPROVER_assume(ok);
  }

  // loop step
  if (tail->next != NULL)
  {
    list_t *old_tail = tail;
    tail = tail->next;
    assert(INC_A1(tail));
    __CPROVER_assume(false);
  }

  assert(x == old_x); // must pass
  assert(x != old_x); // must fail

  #ifndef BUG1
  tail->next = y;
  #endif
  #ifdef BUG2
  y->next = x;
  #endif
}

int main() {

  // build first list
  list_t *x = SEL_A1;
  {
    a11.next = nondet_bool() ? SEL_A1 : NULL;
    a13.next = nondet_bool() ? SEL_A1 : NULL;
    a13.next = nondet_bool() ? SEL_A1 : NULL;
    a14.next = nondet_bool() ? SEL_A1 : NULL;
    a15.next = nondet_bool() ? SEL_A1 : NULL;
    a16.next = nondet_bool() ? SEL_A1 : NULL;
    a17.next = nondet_bool() ? SEL_A1 : NULL;
  }

  // build second list
  list_t *y = SEL_A2;
  {
    a21.next = nondet_bool() ? SEL_A2 : NULL;
    a23.next = nondet_bool() ? SEL_A2 : NULL;
    a23.next = nondet_bool() ? SEL_A2 : NULL;
    a24.next = nondet_bool() ? SEL_A2 : NULL;
  }

  list_append(x, y);

  // check post lseg(y, null)
  {
    list_t *current = y;
    size_t i = 0;
    bool ok = true;
    while(i < SIZE_A2) {
      if(current == NULL) {
        break;
      }
      if(!INC_A2(current)) {
        ok = false;
        break;
      }
      current = current->next;
      i++;
    }
    assert(ok);
  }

  // check post lseg(x, y)
  {
    list_t *current = x;
    size_t i = 0;
    bool ok = true;
    while(i < SIZE_A1) {
      if(current == y) {
        break;
      }
      if(!INC_A1(current)) {
        ok = false;
        break;
      }
      current = current->next;
      i++;
    }
    assert(ok);
  }
  return 0;
}