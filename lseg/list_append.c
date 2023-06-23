#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>
#include "list.h"
#include "lseg.h"
#include "../pointer_predicates.h"

void list_append(list_t *x, list_t *y)
// requires lseg(x, NULL)
// requires lseg(y, NULL)
// ensures lseg(y, NULL) && lseg(x, y)
{
  // x = [fresh0]-> NULL
  // x = [fresh0]-> [opaque0] with lseg(&opaque0, NULL)
  if (x->next == NULL) {
    x->next = y;
    return;
  }
  list_t *tail = x->next;
  while (tail->next != NULL)
  // assigns tail
  // invariant lseg(x, tail) && lseg(tail, NULL)
  // holds because unwinding lseg(x, null) into is_fresh(x) && (x->next == NULL || lseg(x->next, NULL))
  // and kwowing that x->next != NULL) entails lseg(x->next, NULL)
  // and tail == x->next entails lseg(x, tail)
  {
    tail = tail->next;
  }
  // here we have lseg(x, tail) && lseg(tail, NULL) && tail->next == NULL
  tail->next = y;
  // we now have lseg(x, tail) && lseg(tail, y) && lseg(y, NULL)
  // we need to prove
  // lseg(x, y) && lseg(y, NULL)
  // using the lemma lseg(x, tail) && lseg(tail, y) ==> lseg(x, y)
}

void __list_append_check(list_t *x, list_t *y) {
  {
    size_t lh = 2;
    __CPROVER_context_t *ctx = __CPROVER_context_new(true);
    // assume lseg(x, NULL)
    __CPROVER_assume(__lseg(&x, NULL, ctx, lh));
    // assume lseg(y, NULL)
    __CPROVER_assume(__lseg(&y, NULL, ctx, lh));
  }
  __list_append(x, y);
  {
    size_t lh = 2;
    __CPROVER_context_t *ctx = __CPROVER_context_new(false);
    // assert lseg(y, NULL)
    assert(__lseg(&y, NULL, ctx, lh));
    // assert lseg(x, y)
    assert(__lseg(&x, y, ctx, lh));
  }
}

int main_list_append() {
  __lseg_map_init();
  list_t *x;
  list_t *y;
  __list_append_check(x, y);
  return 0;
}