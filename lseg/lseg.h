#ifndef LSEG_H_INCLUDED
#define LSEG_H_INCLUDED
#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>
#include "list.h"
#include "../pointer_predicates.h"

// assumption
typedef struct __lseg_s{
  list_t *x;
  list_t *y;
} __lseg_t;

// ghost map used to track assuptions
__lseg_t *__lseg_map;

// initialise assumptions
void __lseg_map_init() {
  __lseg_map = malloc(__CPROVER_max_symex_objects() * sizeof(__lseg_t));
  __lseg_t zero = (__lseg_t){.x = NULL, .y = NULL};
  __CPROVER_array_set(__lseg_map, zero);
}

// true iff the pointer has an assiciated lseg assumption
bool __lseg_assumed(list_t *x, list_t *y) {
  assert(__CPROVER_r_ok(x, 0));
  assert(y == NULL || __CPROVER_r_ok(y, 0));
  __lseg_t a = __lseg_map[__CPROVER_POINTER_OBJECT(x)];
  return a.x == x && a.y == y;
}

bool nondet_bool();

// after calling this function, ptr is either NULL or an opaque pointer
// assumed to satisfy the lseg predicate
bool __assume_lseg(list_t *x, list_t *y) {
  if (nondet_bool())
    return false;
  assert(__CPROVER_r_ok(x, 0));
  assert(y == NULL || __CPROVER_r_ok(y, 0));
  __lseg_map[__CPROVER_POINTER_OBJECT(x)] = (__lseg_t){.x = x, .y = y};
  return true;
}

// [x]->...->[y]
// bool lseg(list_t *x, list_t *y) {
//   return is_fresh(x, sizeof(*x)) && (equals(x->next, y) || lseg(x->next, y));
// }

// the user-defined predicate is rewritten to operate on a bounded lookahead
// and be assume/assert context sensitive
bool __lseg(list_t **x, list_t *y, __CPROVER_context_t *ctx, size_t lookahead) {
  // assert(y == NULL || __CPROVER_r_ok(y, 0));

  // fail
  if (lookahead == 0) {
    __CPROVER_assert(false,
                     "lookahead bound must be strictly greater than zero");
    return false;
  }

  // lookahead depth reached in assumption context, allocate an opaque pointer
  if (ctx->assume && lookahead == 1) {
    void *opaque = malloc(0);
    __CPROVER_assume(opaque);
    *x = opaque;
    return __assume_lseg(opaque, y);
  }

  // opaque pointer with assumption reached in an assertion context
  if (!ctx->assume && (*x != NULL) && __lseg_assumed(*x, y)) {
    return true;
  }

  // in assumption or assertion contexts, when the lookahead depth is not
  // reached and the pointer is not opaque, just evaluate the definition
  return __is_fresh(x, sizeof(list_t), ctx) &&
         (__pointer_equals(&((*x)->next), y, ctx) ||
          __lseg(&((*x)->next), y, ctx, lookahead - 1));
}

// lemma function
void lseg_lemma(list_t *x, list_t *y, list_t *z);
// requires z == null || fresh(z)
// requires lseg(y, z)
// requires lseg(x, y)
// ensures lseg(x, z)

void __lseg_lemma(list_t *x, list_t *y, list_t *z)
{
  // unwind lseg(x, y)
  // x = [fresh0]->y
  // x = [fresh0]->opaque0 with lseg(opaque0, y)
  if (x->next != y) {
    // requires lseg(y, z) // by lemma preconditions
    // requires lseg(x->next, y)
    // holds because x->next == opaque0 with assumption lseg(opaque0, y)
    return lseg_lemma(x->next, y, z);
    // ensures lseg(x->next, z)
    // derive lseg(x, z) by folding is_fresh(x) && lseg(x->next, z)
  } else {
    // derive lseg(x, z) by folding
    // is_fresh(x) && x->next == y && lseg(y, z)
    return;
  }
}

static bool __lseg_lemma_on_stack = false;

// using the lemma consists in checking that premises hold and emitting the conclusion
void use_lseg_lemma(list_t *x, list_t *y, list_t *z) {
  {
    size_t lh = 2;
    __CPROVER_context_t *ctx = __CPROVER_context_new(false);
    // assert z == null || fresh(z)
    assert(__pointer_equals(&z, NULL, ctx) || __is_fresh(&z, sizeof(*z), ctx));
    // assert lseg(y, z)
    assert(__lseg(&y, z, ctx, lh));
    // assert lseg(x, y)
    assert(__lseg(&x, y, ctx, lh));
  }
  {
    __CPROVER_assume(__assume_lseg(x, z));
  }
}

void lseg_lemma(list_t *x, list_t *y, list_t *z) {
  if(!__lseg_lemma_on_stack) {
    {
      size_t lh = 2;
      __CPROVER_context_t *ctx = __CPROVER_context_new(true);
      // assume z == null || fresh(z)
      __CPROVER_assume(__pointer_equals(&z, NULL, ctx) ||
                       __is_fresh(&z, sizeof(*z), ctx));
      // assume lseg(y, z)
      __CPROVER_assume(__lseg(&y, z, ctx, lh));
      // assume lseg(x, y)
      __CPROVER_assume(__lseg(&x, y, ctx, lh));
    }
    __lseg_lemma_on_stack = true;
    __lseg_lemma(x, y, z);
    __lseg_lemma_on_stack = false;
    {
      size_t lh = 1;
      __CPROVER_context_t *ctx = __CPROVER_context_new(false);
      // assume z == null || fresh(z)
      assert(__pointer_equals(&z, NULL, ctx) ||
             __is_fresh(&z, sizeof(*z), ctx));

      // // assert lseg(x, z)
      // assert(__lseg(&x, z, ctx, lh));
    }
  } else {
    use_lseg_lemma(x, y, z);
  }
}

int main_lseg_lemma() {
  __lseg_map_init();
  list_t *x;
  list_t *y;
  list_t *z;
  lseg_lemma(x, y, z);
  return 0;
}

#endif