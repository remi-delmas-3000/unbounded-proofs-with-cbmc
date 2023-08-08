#ifndef LSEG_H_INCLUDED
#define LSEG_H_INCLUDED
#include "../pointer_predicates.h"
#include "list.h"
#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

// // fresh1 -> y
// // fresh1 -> fresh2 -> ... -> y
// bool lseg(x, y) {
//   is_fresh(x) && (equals(x->next, y) || lseg(x->next, y));
// }

// assumption
typedef struct __lseg_s {
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

// [x]->...->[y] where y is defined by some other constraint
// bool lseg(list_t *x, list_t *y) {
//   return is_fresh(x, sizeof(*x)) && (equals(x->next, y) || lseg(x->next, y));
// }

// the user-defined predicate is rewritten to operate on a bounded lookahead
// and be assume/assert context sensitive
bool __lseg(list_t **x, list_t *y, __CPROVER_context_t *ctx, size_t lookahead) {
  // fail
  if (lookahead == 0) {
    __CPROVER_assert(false,
                     "lookahead bound must be strictly greater than zero");
    return false;
  }

  // lookahead depth reached in assumption context, allocate an opaque pointer
  if (ctx->assume && lookahead == 1) {
    list_t *opaque = (list_t *)malloc(0);
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
  return __is_fresh((void **)x, sizeof(list_t), ctx) &&
         (__pointer_equals((void **)&((*x)->next), y, ctx) ||
          __lseg(&((*x)->next), y, ctx, lookahead - 1));
}

// [x]->...->[y] where y is null or fresh
// bool lseg2(list_t *x, list_t *y) {
//  return (equals(y, NULL) || is_fresh(y)) && lseg(x, y)
// }
// the user-defined predicate is rewritten to operate on a bounded lookahead
// and be assume/assert context sensitive
// bool __lseg2(list_t **x, list_t **y, __CPROVER_context_t *ctx,
//              size_t lookahead) {
//   return (__pointer_equals((void **)y, NULL, ctx) ||
//           __is_fresh((void **)y, sizeof(list_t), ctx)) &&
//          __lseg(y, y, ctx, lookahead);
// }

// lemma function
// requires z == null || fresh(z)
// requires lseg(y, z)
// requires lseg(x, y)
// requires z == null || fresh(z)
// ensures lseg(x, z)
void lseg_lemma(list_t *x, list_t *y, list_t *z);

void __lseg_lemma(list_t *x, list_t *y, list_t *z) {
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

// using the lemma consists in checking that premises hold and emitting the
// conclusion
void use_lseg_lemma(list_t *x, list_t *y, list_t *z, size_t lh_pre,
                    size_t lh_post) {
  __CPROVER_assert(lh_pre > 0, "lh_pre >  1");
  __CPROVER_assert(lh_post > 0, "lh_post > 1");
  // check preconditions
  __CPROVER_context_t *ctx = __CPROVER_context_new(false);
  __CPROVER_assert(__pointer_equals(&z, NULL, ctx) ||
                       __is_fresh(&z, sizeof(*z), ctx),
                   "lseg lemma precondition z == NULL || is_fresh(z)");
  __CPROVER_assert(__lseg(&y, z, ctx, lh_pre),
                   "lseg lemma precondition lseg(x, y)");
  __CPROVER_assert(__lseg(&x, y, ctx, lh_pre),
                   "lseg lemma precondition lseg(y, z)");

  // emit lemma post-conditions
  __CPROVER_assume(__assume_lseg(x, z));
}

void lseg_lemma(list_t *x, list_t *y, list_t *z) {
  if (!__lseg_lemma_on_stack) {
    {
      // assume preconditions
      size_t lh = 2;
      __CPROVER_context_t *ctx = __CPROVER_context_new(true);

      // unwind  z == null || z == fresh0
      __CPROVER_assume(__pointer_equals((void **)&z, NULL, ctx) ||
                       __is_fresh((void **)&z, sizeof(*z), ctx));

      // unwind lseg(y, z)
      // y = [fresh1]->z
      // y = [fresh1]->opaque0 with lseg_assumed(opaque0, z)
      __CPROVER_assume(__lseg(&y, z, ctx, lh));

      // unwind lseg(x, y)
      // x = [fresh2]->y
      // x = [fresh2]->opaque1 with lseg_assumed(opaque1, y)
      __CPROVER_assume(__lseg(&x, y, ctx, lh));
    }

    // call function under verification
    __lseg_lemma_on_stack = true;
    __lseg_lemma(x, y, z);
    __lseg_lemma_on_stack = false;

    {
      // check post condition
      size_t lh = 3;
      __CPROVER_context_t *ctx = __CPROVER_context_new(false);
      // assume z == null || fresh(z)
      assert(__pointer_equals(&z, NULL, ctx) ||
             __is_fresh(&z, sizeof(*z), ctx));

      // assert lseg(x, z)
      assert(__lseg(&x, z, ctx, lh));
    }
  } else {
    use_lseg_lemma(x, y, z, 2, 1);
  }
}

#endif
