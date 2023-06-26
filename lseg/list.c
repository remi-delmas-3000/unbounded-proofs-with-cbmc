#include "list.h"
#include "../pointer_predicates.h"
#include "lseg.h"
#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

// requires lseg(x, NULL)
// requires lseg(y, NULL)
// ensures lseg(y, NULL)
// ensures lseg(x, y)
void __list_append(list_t *x, list_t *y) {
  // x = [fresh0]-> NULL
  // x = [fresh0]-> [opaque0] with lseg(&opaque0, NULL)
  if (x->next == NULL) {
    x->next = y;
    return;
  }

  list_t *tail = x->next;

  {
    // loop invariant base case
    size_t lh = 2;
    __CPROVER_context_t *ctx = __CPROVER_context_new(false);

    // assert lseg(tail, NULL)
    __CPROVER_assert(__lseg(&tail, NULL, ctx, lh), "loop invariant base case");

    // assert lseg(x, tail)
    __CPROVER_assert(__lseg(&x, tail, ctx, lh), "loop invariant base case");
  }

  {
    // assume loop invariant step case
    size_t lh = 2;
    __CPROVER_context_t *ctx = __CPROVER_context_new(false);

    // __CPROVER_assume lseg(tail, NULL)
    __CPROVER_assume(__lseg(&tail, NULL, ctx, lh));

    // __CPROVER_assume lseg(x, tail)
    __CPROVER_assume(__lseg(&x, tail, ctx, lh));

    // note:
    // this allocates a fresh object for tail which models an arbitrary object
    // in the list

    // tail = [fresh0]->NULL
    // tail = [fresh0]->[opaque0] with lseg_assumed(opaque0, NULL)

    // this also allocates a fresh object for x, eventhough x is not modified by
    // the loop

    // x = [fresh1]->[tail]
    // x = [fresh1]->[opaque1] with lseg_assumed(opaque1, tail)

    // the actual identity of objects is not important. What matters is that
    // this models an arbitrary state where the pointers are satisfying the loop
    // invariant: from tail by following next pointers we eventually reach NULL
    // and from x we evenually reach tail.
  }

  if (tail->next != NULL)
  // assigns tail
  // invariant lseg(x, tail) && lseg(tail, NULL)
  // holds because unwinding lseg(x, null) into is_fresh(x) && (x->next == NULL
  // || lseg(x->next, NULL)) and kwowing that x->next != NULL) entails
  // lseg(x->next, NULL) and tail == x->next entails lseg(x, tail)
  {
    tail = tail->next;
    {
      // loop invariant step case
      size_t lh = 2;
      __CPROVER_context_t *ctx = __CPROVER_context_new(false);

      // assert lseg(tail, NULL)
      __CPROVER_assert(__lseg(&tail, NULL, ctx, lh),
                       "loop invariant step case");

      // assert lseg(x, tail)
      __CPROVER_assert(__lseg(&x, tail, ctx, lh), "loop invariant step case");
    }

    __CPROVER_assume(false);
  }

  // loop invariant && !guard holds
  // lseg(x, tail) && lseg(tail, NULL) && tail->next == NULL
  tail->next = y;
  // post : lseg(x, tail) && lseg(tail, y) && lseg(y, NULL)

  // to establish the post lseg(x, y) && lseg(y, NULL)
  // we use the lseg transitivity lemma

  // requires y == null || is_fresh(y)
  // requires lseg(tail, y)
  // requires lseg(x, tail)
  use_lseg_lemma(x, tail, y, 2, 1);
  // ensures lseg(x, y)
}

void list_append(list_t *x, list_t *y) {
  {
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

  {
    // check postconditions
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