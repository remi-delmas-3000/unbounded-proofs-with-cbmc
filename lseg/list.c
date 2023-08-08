#include "list.h"
#include "../pointer_predicates.h"
#include "lseg.h"
#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

// bool distinct(void *);

// bool lseg_pred(list_t *x, list_t *y)
// {
//   return distinct(x) && (x->next == y || lseg_pred(x->next, y));
// }


// requires lseg(x, null)
// requires lseg(y, null)
// ensures lseg(y, null)
// ensures lseg(x, y)
void list_append_base(list_t *x,list_t *y) {
  if (x->next == NULL) {
    x->next = y;
    return;
  }
  list_t *tail = x->next;
  list_t *old_x = x;

  while (tail->next != NULL)
  // assigns tail
  // loop invariant lseg(x, tail) && lseg(tail, NULL)
  {
    #ifdef CBMC
    list_t *tail_old = tail; // tail_old in {A1}
    #endif
    tail = tail->next;
    // x in {A1}
    // x->next in {A1, NULL}
    // tail_old in {A1}
    // tail in {A1}
    // tail->next in {A1, NULL}
    #ifdef CBMC
    // use_lseg_lemma(x, tail_old, tail);
    #endif
  }

  // x in {A1}
  // x->next in {A1, NULL}
  // tail in {A1}
  // tail->next in {NULL}

  // here lseg(x, tail) && lseg(tail, NULL) && tail->next == NULL
  tail->next = y;
  assert(x != old_x); // must fail
  assert(x == old_x); // must pass

  // here lseg(x, tail) && lseg(tail, y)
  // use_lseg_lemma(x, tail, y)
  // assume lseg(x, y)
  // post: lseg(x, y) && lseg(y, null)
}

// requires lseg(x, NULL)
// requires lseg(y, NULL)
// ensures lseg(y, NULL)
// ensures lseg(x, y)
void __list_append(list_t *x, list_t *y) {
  // y = [fresh0]->NULL
  // y = [fresh0]->[opaque0] with lseg_assumed(opaque0, NULL)


  // x = [fresh1]-> NULL
  if (x->next == NULL) {
    x->next = y;
    return;
  }

  list_t *tail = x->next;
  list_t *old_x = x;

  // x = [fresh1]-> [opaque1] with lseg(opaque1, NULL)
  // tail = [opaque0]
  if(true) {
    // loop invariant base case
    size_t lh = 2;
    __CPROVER_context_t *ctx = __CPROVER_context_new(false);

    // assert lseg(tail, NULL)
    __CPROVER_assert(__lseg(&tail, NULL, ctx, lh), "loop invariant base case");

    // assert lseg(x, tail)
    __CPROVER_assert(__lseg(&x, tail, ctx, lh), "loop invariant base case");
  }

  if(true) {
    // havoc the loop state
    // Note: this allocates a fresh object for tail which models an arbitrary
    // object in the list. This also allocates a fresh object for x, eventhough
    // x is not modified by the loop. The actual identity of objects is not
    // important. What matters is that this models an arbitrary state where the
    // pointers are satisfying the loop invariant: from tail by following next
    // pointers we eventually reach NULL and from x we evenually reach tail.

    size_t lh = 3;
    __CPROVER_context_t *ctx = __CPROVER_context_new(true);
    // __CPROVER_assume lseg(tail, NULL)
    __CPROVER_assume(__lseg(&tail, NULL, ctx, lh));
    // __CPROVER_assume lseg(x, tail)
    __CPROVER_assume(__lseg(&x, tail, ctx, lh));
    // tail = [fresh2]->NULL
    // tail = [fresh2]->[opaque2] with lseg_assumed(opaque2, NULL)
    // x = [fresh3]->[fresh2]
    // x = [fresh3]->[opaque3] with lseg_assumed(opaque3, fresh2)
  }

  if (tail->next != NULL)
  // assigns tail
  // invariant lseg(x, tail) && lseg(tail, NULL)
  // holds because unwinding lseg(x, null) into is_fresh(x) && (x->next == NULL
  // || lseg(x->next, NULL)) and kwowing that x->next != NULL) entails
  // lseg(x->next, NULL) and tail == x->next entails lseg(x, tail)
  {
    // tail = [fresh2]->[opaque2] with lseg_assumed(opaque2, NULL)
    list_t *tail_old = tail;
    tail = tail->next;
    // tail = [opaque2] with lseg_assumed(opaque2, NULL)
    if (true) {
      // loop invariant step case
      size_t lh = 3;
      __CPROVER_context_t *ctx = __CPROVER_context_new(false);

      // assert lseg(tail, NULL)
      __CPROVER_assert(__lseg(&tail, NULL, ctx, lh),
                       "loop invariant step case");

      // // assert lseg(x, tail)
      // x = [fresh3]->[tail_old]
      // x = [fresh3]->[opaque3] with lseg(opaque3, tail_old) lseg(tail_old, tail)
      use_lseg_lemma(x, tail_old, tail, lh, 2);
      __CPROVER_assert(__lseg(&x, tail, ctx, lh), "loop invariant step case");
    }

    __CPROVER_assume(false);
  }

  // loop invariant && !guard holds
  // lseg(x, tail) && lseg(tail, NULL) && tail->next == NULL
  tail->next = y;
  // post : lseg(x, tail) && lseg(tail, y) && lseg(y, NULL)

  if (true) {
    assert(x == old_x); // should pass but fails because x now points to the
                        // object allocated to model the loop step
    assert(x != old_x); // should fail but passes because of the same reason
  }

  // to establish the post lseg(x, y) && lseg(y, NULL)
  // we use the lseg transitivity lemma

  // requires y == null || is_fresh(y)
  // requires lseg(tail, y)
  // requires lseg(x, tail)
  use_lseg_lemma(x, tail, y, 3, 1);
  // ensures lseg(x, y)

  // the posconditions hold in this context because
  // x points to fresh objects satisfying the loop invariant
  if (true) {
    size_t lh = 3;
    __CPROVER_context_t *ctx = __CPROVER_context_new(false);
    // assert lseg(y, NULL)
    assert(__lseg(&y, NULL, ctx, lh));
    // assert lseg(x, y)
    assert(__lseg(&x, y, ctx, lh));
  }
}

void list_append(list_t *x, list_t *y) {
  if (true) {
    // assume preconditions
    size_t lh = 3;
    __CPROVER_context_t *ctx = __CPROVER_context_new(true);
    // assume lseg(x, NULL)
    __CPROVER_assume(__lseg(&x, NULL, ctx, lh));
    // assume lseg(y, NULL)
    __CPROVER_assume(__lseg(&y, NULL, ctx, lh));
  }

  // call function
  __list_append(x, y);

  // should pass but fails in this scope because x still points
  // to the objects allocated by the precondition,
  // and not to the fresh objects instantiated to model the loop step and
  // invariant
  if (true) {
    size_t lh = 3;
    __CPROVER_context_t *ctx = __CPROVER_context_new(false);
    // assert lseg(y, NULL)
    assert(__lseg(&y, NULL, ctx, lh));
    // assert lseg(x, y)
    assert(__lseg(&x, y, ctx, lh));
  }
}

int main() {
  // initialise assumptions map
  __lseg_map_init();

  list_t *x;
  list_t *y;
  list_append(x, y);
  return 0;
}