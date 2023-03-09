#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

#include "write_set.h"
#include "pointer_predicates.h"

/*

/// list node data type
typedef struct list_s {
  int value;
  int hidden_field;
  struct list_s *next;
} list_t;

/// User-defined pointer predicate that encodes the shape of the list.
bool is_list(list_t *list) {
  return __CPROVER_is_fresh(list, sizeof(list_t)) &&
                             __CPROVER_assignable_int(&(list->value)) &&
                             #ifdef FIX_ASSIGN_HIDDEN
                             __CPROVER_assignable_int(&(list->hidden)) &&
                             #endif
                             (list->next == NULL || is_list(list->next));
}

/// traverse the list and assign its value.
/// Assigns hidden field and triggers a frame condition violation if
/// ASSIGN_HIDDEN is defined
void list_init(list_t *list, int value)
__requires(list == NULL || is_list(list))
{
  if (!list)
    return;
  // will succeed
  list->value = value;
#ifdef ASSIGN_HIDDEN
  // will fail
  list->hidden_field = 0;
#endif
  list_init(list->next, value);
}

*/


// The code below shows:
// - the inductive formulation of the verification problem
// - unbounded memory predicates instrumentation
// - the dynamic frames instrumentation
// - the proof harness
//
// All of which can (and will) be generated automatically by goto-instrument
//

/// @brief List data type under verification
typedef struct list_s {
  int value;
  int hidden;
  struct list_s *next;
} list_t;

/// Ghost map used to track pointer assumptions
bool *__is_list_assumed_map;

/// @brief Initialises the ghost map to false
void __is_list_assumed_map_init() {
  __is_list_assumed_map = malloc(__CPROVER_max_symex_objects() * sizeof(bool));
  __CPROVER_array_set(__is_list_assumed_map, false);
}

bool nondet_bool();

/// @brief Records the assumption that this pointer variable satisfies the predicate.
/// Turns it into a NULL or non-NULL opaque pointer.
/// @param ptr target pointer
/// @return true
bool __assume_is_list(void *ptr) {
  if(nondet_bool())
    return false;
  assert(__CPROVER_r_ok(ptr, 0));
  __is_list_assumed_map[__CPROVER_POINTER_OBJECT(ptr)] = true;
  return true;
}

/// @brief Assumption lookup function.
/// @param ptr target pointer
/// @return True iff there is an __is_list assumption for this pointer
bool __is_list_assumed(void *ptr) {
  assert(__CPROVER_r_ok(ptr, 0));
  return __is_list_assumed_map[__CPROVER_POINTER_OBJECT(ptr)];
}

// the user-defined predicate is_list is rewritten to operate with
// - context information,
// - write set parameter
// - bounded lookahead
bool __is_list(list_t **list, __CPROVER_context_t *ctx,
               __CPROVER_contracts_write_set_ptr_t write_set,
               size_t lookahead) {
  //// ADDED BY INSTRUMENTATION
  // fail if we went too far
  if (lookahead == 0) {
    __CPROVER_assert(false,
                     "lookahead bound must be strictly greater than zero");
    return false;
  }

  // lookahead depth reached in assumption context, allocate an opaque pointer
  // and store assumption
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

  //// INITIAL DEFINITION
  // in assumption or assertion contexts, when the lookahead depth is not
  // reached and the pointer is not opaque, just evaluate the definition
  return __is_fresh(list, sizeof(list_t), ctx) &&
         __assignable_int(&((*list)->value), ctx, write_set) &&
#ifdef FIX_ASSIGN_HIDDEN
         __assignable_int(&((*list)->hidden), ctx, write_set) &&
#endif
         (__pointer_equals(&((*list)->next), NULL, ctx) ||
          __is_list(&((*list)->next), ctx, write_set, lookahead - 1));
}

/// Verification wrapper function
void list_init(list_t *list, int value, __CPROVER_contracts_write_set_ptr_t write_set);

/// Function under verification
void __list_init(list_t *list, int value, __CPROVER_contracts_write_set_ptr_t write_set) {
  // traverse the list and assign its value fields
  if (!list)
    return;

  // write set lookup (should pass)
  __CPROVER_assert(__CPROVER_contracts_write_set_check_assignment(
                       write_set, &(list->value), sizeof(int)),
                   "list->value is assignable");
  list->value = value;

#ifdef ASSIGN_HIDDEN
  // write set lookup (should fail)
  __CPROVER_assert(__CPROVER_contracts_write_set_check_assignment(
                       write_set, &(list->hidden), sizeof(int)),
                   "list->hidden_field is assignable");
  list->hidden = 0;
#endif

  // recursive call
  list_init(list->next, value, write_set);
}

/// Tracking variable for recursive call
bool __list_init_on_stack = false;

/// VERIFICATION WRAPPER
void list_init(list_t *list, int value,
               __CPROVER_contracts_write_set_ptr_t write_set) {

  if (!__list_init_on_stack) {
    // in a top-level call, assume the requires clause
    __CPROVER_context_t *ctx = __CPROVER_context_new(true);
    // create the dynamic write set instance
    __CPROVER_contracts_write_set_t __write_set;
    __CPROVER_contracts_write_set_ptr_t write_set = &__write_set;
    __CPROVER_contracts_write_set_create(write_set, 2, 0, false, false, false,
                                         false, false, false);

    // assuming the predicate allocates memory and populates the write set.
    __CPROVER_assume(__pointer_equals(&list, NULL, ctx) ||
                     __is_list(&list, ctx, write_set, 2));
    __list_init_on_stack = true;

    // pass the dynamic write set to function under verification
    __list_init(list, value, write_set);
    __list_init_on_stack = false;

    // release the write set
    __CPROVER_contracts_write_set_release(write_set);
    return;
  } else {
    // in a recursive call, assert the requires clause
    __CPROVER_context_t *ctx = __CPROVER_context_new(false);

    // asserting the predicate checks the definition and performs the inclusion
    // check
    __CPROVER_assert(__pointer_equals(&list, NULL, ctx) ||
                         __is_list(&list, ctx, write_set, 2),
                     "recursive call precondition");
    return;
  }
}

/*
run this with:
cbmc --bounds-check --pointer-check --pointer-overflow-check list_init_unbounded.c
and expect it to fail with
[__list_init.assertion.2] line 230 list->hidden_field is assignable: FAILURE
*/

void main() {

  // inialise the global assumption map
  __is_list_assumed_map_init();
  list_t *list;
  int value;

  // call the verification wrapper
  list_init(list, value, NULL);
}
