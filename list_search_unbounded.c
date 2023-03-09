#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>
#include "pointer_predicates.h"

typedef struct list_s {
  int value;
  struct list_s *next;
} list_t;

// ghost maps used to track opaque pointers and assumptions
bool *__is_list_assumed_map;

// initialise the global map to false
void __is_list_assumed_map_init() {
  __is_list_assumed_map = malloc(__CPROVER_max_symex_objects() * sizeof(bool));
  __CPROVER_array_set(__is_list_assumed_map, false);
}

bool nondet_bool();

// after calling this function, ptr is either NULL or an opaque pointer
// assumed to satisfy the is_list predicate
bool __assume_is_list(void *ptr) {
  if(nondet_bool())
    return false;
  assert(__CPROVER_r_ok(ptr, 0));
  __is_list_assumed_map[__CPROVER_POINTER_OBJECT(ptr)] = true;
  return true;
}

// true iff the pointer has an assiciated is_list assumption
bool __is_list_assumed(void *ptr) {
  assert(__CPROVER_r_ok(ptr, 0));
  return __is_list_assumed_map[__CPROVER_POINTER_OBJECT(ptr)];
}


// the user-defined predicate is rewritten to operate on a bounded lookahead
// and be assume/assert context sensitive
bool __is_list(list_t **list, __CPROVER_context_t *ctx, size_t lookahead) {

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
    *list = opaque;
    return __assume_is_list(opaque);
  }

  // opaque pointer reached in an assertion context
  if (!ctx->assume && (*list != NULL) && __is_list_assumed(*list)) {
    return true;
  }

  // in assumption or assertion contexts, when the lookahead depth is not
  // reached and the pointer is not opaque, just evaluate the definition
  return __is_fresh(list, sizeof(list_t), ctx) &&
         (__pointer_equals(&((*list)->next), NULL, ctx) ||
          __is_list(&((*list)->next), ctx, lookahead - 1));
}

bool list_search(list_t *list, int value);

// function under verification
bool __list_search(list_t *list, int value) {
  return list && ((list->value == value) || list_search(list->next, value));
}

// verification wrapper
bool __list_search_on_stack = false;

bool list_search(list_t *list, int value) {
  if (!__list_search_on_stack) {
    // assume we have an unbounded list
    __CPROVER_context_t *ctx = __CPROVER_context_new(true);
    __CPROVER_assume(__pointer_equals(&list, NULL, ctx) || __is_list(&list, ctx, 3));
    __list_search_on_stack = true;
    bool __retval = __list_search(list, value);
    __list_search_on_stack = false;
    return __retval;
  } else {
    // prove we have an unbounded list
    __CPROVER_context_t *ctx = __CPROVER_context_new(false);
    __CPROVER_assume(__pointer_equals(&list, NULL, ctx) || __is_list(&list, ctx, 3));
    bool __retval = nondet_bool();
    return __retval;
  }
}

/*
cbmc --bounds-check --pointer-check --pointer-overflow-check --external-sat-solver kissat list_search_unbounded.c
*/
void main() {
  __is_list_assumed_map_init();
  list_t *list;
  int value;
  list_search(list, value);
}
