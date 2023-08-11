/* list append verification using the abstract objects program transformation */
#include "list.h"
// #include "../pointer_predicates.h"
// #include "lseg.h"
#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

/*
// The semantics of lseg(x, y) is given in terms of abstract objects and
// points-to sets
// Abstract objects X, Y
// PT(x) = {&X}
// PT(X.next) = {&X, &Y}

// preconditions lseg(x, null) and lseg(y, null) generate X and Y and the
// following points to sets
// PT(x) = {&X};
// PT(x->next) = {&X, null}
// PT(y) = {&Y};
// PT(tail) = {}
// PT(tail->next) = {}
// PT(old_x) = {}
// PT(old_tail) = {}
// PT(X.next) = {&X, null};
// PT(Y.next) = {&Y, null};

void list_append_orig(list_t *x,list_t *y)
// requires lseg(x, null)
// requires lseg(y, null)
// ensures lseg(y, null)
// ensures lseg(x, y)
{
  // PT(x) = {&X}
  // PT(x->next) = {&X, null}
  // PT(y) = {&Y}
  // PT(tail) = {}
  // PT(tail->next) = {}
  // PT(old_x) = {}
  // PT(old_tail) = {}
  // PT(X.next) = {&X, null}
  // PT(Y.next) = {&Y, null}
  // |X| = 3
  // |Y| = 2
  if (x->next == NULL) {
    // PT(x) = {&X}
    // PT(x->next) = {null}
    // PT(y) = {&Y}
    // PT(tail) = {}
    // PT(tail->next) = {}
    // PT(old_x) = {}
    // PT(old_tail) = {}
    // PT(X.next) = {null}
    // PT(Y.next) = {&Y, null}
    // |X| = 1
    // |Y| = 2
    x->next = y;
    // PT(x) = {&X}
    // PT(x->next) = {&Y}
    // PT(y) = {&Y}
    // PT(tail) = {}
    // PT(tail->next) = {}
    // PT(old_x) = {}
    // PT(old_tail) = {}
    // PT(X.next) = {&Y}
    // PT(Y.next) = {&Y, null}
    // |X| = 1
    // |Y| = 4
    return;
  }
  // PT(x) = {&X}
  // PT(x->next) = {&X}
  // PT(y) = {&Y}
  // PT(tail) = {}
  // PT(tail->next) = {}
  // PT(old_x) = {}
  // PT(old_tail) = {}
  // PT(X.next) = {&X};
  // PT(Y.next) = {&Y, null};
  // |X| = 3
  // |Y| = 2

  list_t *tail = x->next;
  list_t *old_x = x;

  // PT(x) = {&X}
  // PT(x->next) = {&X}
  // PT(y) = {&Y}
  // PT(tail) = {&X}
  // PT(tail->next) = {&X, null}
  // PT(old_x) = {&X}
  // PT(old_tail) = {}
  // PT(X.next) = {&X};
  // PT(Y.next) = {&Y, null};
  // |X| = 6
  // |Y| = 2

  while (tail->next != NULL)
  // fixpoint
  // PT(x) = {&X}
  // PT(x->next) = {&X}
  // PT(y) = {&Y}
  // PT(tail) = {&X}
  // PT(tail->next) = {&X}
  // PT(old_x) = {&X}
  // PT(old_tail) = {&X}
  // PT(X.next) = {&X};
  // PT(Y.next) = {&Y, null};
  // |X| = 7
  // |Y| = 2

  // assigns tail
  // loop invariant lseg(x, tail) && lseg(tail, NULL)
  {

    list_t *old_tail = tail;
    tail = tail->next;
    // fixpoint
    // PT(x) = {&X}
    // PT(x->next) = {&X}
    // PT(y) = {&Y}
    // PT(tail) = {&X}
    // PT(tail->next) = {&X, null}
    // PT(old_x) = {&X}
    // PT(old_tail) = {&X}
    // PT(X.next) = {&X};
    // PT(Y.next) = {&Y, null};
    // |X| = 7
    // |Y| = 2
  }
  // post loop
  // PT(x) = {&X}
  // PT(x->next) = {&X}
  // PT(y) = {&Y}
  // PT(tail) = {&X}
  // PT(tail->next) = {null}
  // PT(old_x) = {&X}
  // PT(old_tail) = {&X}
  // PT(X.next) = {&X};
  // PT(Y.next) = {&Y, null};
  // |X| = 6
  // |Y| = 2
  tail->next = y;
  // PT(x) = {&X}
  // PT(x->next) = {&X}
  // PT(y) = {&Y}
  // PT(tail) = {&X}
  // PT(tail->next) = {&Y}
  // PT(old_x) = {&X}
  // PT(old_tail) = {&X}
  // PT(X.next) = {&X};
  // PT(Y.next) = {&Y, null};
  // |X| = 6
  // |Y| = 2
  assert(x == old_x); // must pass
  assert(x != old_x); // must fail
}
*/

// concretisation of X
list_t x1;
list_t x2;
list_t x3;
list_t x4;
list_t x5;
list_t x6;
list_t x7;
#define SIZE_X 7
#define SEL_X                                                                 \
  (nondet_bool()   ? &x1                                                      \
   : nondet_bool() ? &x2                                                      \
   : nondet_bool() ? &x3                                                      \
   : nondet_bool() ? &x4                                                      \
   : nondet_bool() ? &x5                                                      \
   : nondet_bool() ? &x6                                                      \
                   : &x7)
#define INC_X(X)                                                              \
  ((X == &x1) || (X == &x2) || (X == &x3) || (X == &x4) || (X == &x5) ||  \
   (X == &x6) || (X == &x7))

// concretisation of Y
list_t y1;
list_t y2;
list_t y3;
list_t y4;
#define SIZE_Y 4
#define SEL_Y                                                                 \
  (nondet_bool() ? &y1 : nondet_bool() ? &y2 : nondet_bool() ? &y3 : &y4)
#define INC_Y(X) ((X == &y1) || (X == &y2) || (X == &y3) || (X == &y4))


// transformed program
void list_append(list_t *x, list_t *y) {

  if (x->next == NULL) {
    x->next = y;
    return;
  }

  list_t *tail = x->next;
  list_t *old_x = x;

  // check base case lseg(tail, null)
  {
    // lseg(tail, null)
    assert(INC_X(tail));
    assert(INC_X(tail->next) || tail->next == NULL);
    // vacuity check
    __CPROVER_assert(tail->next != NULL, "FAILURE");
  }

  // check base case lseg(x, tail)
  {
    assert(INC_X(x));
    assert(INC_X(tail));
    assert(INC_X(x->next) || x->next == tail);
    // vacuity check
    __CPROVER_assert(x->next != tail, "FAILURE");
  }

  // loopback tail
  tail = nondet_bool() ? SEL_X : tail;

  // assume step case lseg(tail, null)
  {
    __CPROVER_assume(INC_X(tail->next) ||  tail->next == NULL);
    // vacuity check
    __CPROVER_assert(tail->next != NULL, "FAILURE");
  }

  // assume step case lseg(x, tail)
  {
    __CPROVER_assume(INC_X(x));
    __CPROVER_assume(INC_X(x->next) || x->next == tail);
    // vacuity check
    __CPROVER_assert(x->next != tail, "FAILURE");
  }
  // now [x]-> X ->[tail]-> X -> null
  // loop step
  if (tail->next != NULL)
  {
    list_t *old_tail = tail;
    tail = tail->next;
    // loop invariant
    assert(INC_X(tail));
    assert(INC_X(tail->next) || tail->next == NULL);
    assert(INC_X(x));
    assert(INC_X(x->next) || x->next == tail);
    // vacuity check
    __CPROVER_assert(tail->next != NULL, "FAILURE");
    __CPROVER_assert(x->next != tail, "FAILURE");
    __CPROVER_assume(false);
  }
  assert(tail->next == NULL);
  assert(x == old_x); // must pass
  __CPROVER_assert(x != old_x, "FAILURE");

  #if 0
  tail->next = y;
  #endif

  #if BUG2
  y->next = x;
  #endif
}

int main() {

  // build first list
  list_t *x = SEL_X;
  {
    // lseg(X, null)
    x1.next = nondet_bool() ? SEL_X : NULL;
    x3.next = nondet_bool() ? SEL_X : NULL;
    x3.next = nondet_bool() ? SEL_X : NULL;
    x4.next = nondet_bool() ? SEL_X : NULL;
    x5.next = nondet_bool() ? SEL_X : NULL;
    x6.next = nondet_bool() ? SEL_X : NULL;
    x7.next = nondet_bool() ? SEL_X : NULL;
  }

  // build second list
  list_t *y = SEL_Y;
  {
    // lseg(Y, null)
    // forall a: Y, a.next == &Y || a.next == NULL
    y1.next = nondet_bool() ? SEL_Y : NULL;
    y3.next = nondet_bool() ? SEL_Y : NULL;
    y3.next = nondet_bool() ? SEL_Y : NULL;
    y4.next = nondet_bool() ? SEL_Y : NULL;
  }

  list_append(x, y);

  // check post lseg(y, null)
  assert(INC_Y(y));
  assert(INC_Y(y->next) || y->next == NULL);
  __CPROVER_assert(y->next != NULL, "FAILURE");


  // check post lseg(x, y)
  assert(INC_X(x));
  assert(INC_X(x->next) || INC_Y(x->next));
  return 0;
}
