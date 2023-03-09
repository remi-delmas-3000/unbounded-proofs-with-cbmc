#ifndef __CPROVER_pointer_predicates_defined
#define __CPROVER_pointer_predicates_defined
#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>
#include "write_set.h"

bool nondet_bool();
__CPROVER_size_t nondet_size_t();

extern __CPROVER_size_t __CPROVER_max_malloc_size;
int __builtin_clzll(unsigned long long);

// Maximum number of objects that can exist in CBMC's symex.
unsigned long long __CPROVER_max_symex_objects() {
  int object_bits = __builtin_clzll(__CPROVER_max_malloc_size);
  return 1ULL << object_bits;
}

/// @brief Context tracking structure for memory predicates evaluation.
typedef struct {
  /// assumption mode on/off
  bool assume;
  /// map of seen objects
  bool *is_fresh_seen;
  /// append-list of size of fresh objects
  __CPROVER_size_t *is_fresh_size;
  /// append-list of pointers to fresh objects
  void **is_fresh_ptr;
  /// number of fresh objects
  __CPROVER_size_t nof_fresh;
} __CPROVER_context_t;

bool __is_fresh(void **ptr, __CPROVER_size_t size, __CPROVER_context_t *ctx);
bool __pointer_equals(void **ptr1, void *ptr2, __CPROVER_context_t *ctx);
bool __null_or_seen(void **ptr, __CPROVER_context_t *ctx);
bool __pointer_in_range(void *lb, void **ptr, void *ub,
                        __CPROVER_context_t *ctx);
bool __assignable_int(int *ptr, __CPROVER_context_t *ctx,
                      __CPROVER_contracts_write_set_ptr_t write_set);

/// @brief Initialises memory predicates context.
/// @param assume assumption mode on/off
/// @return a fresh context instance
__CPROVER_context_t *__CPROVER_context_new(bool assume) {
  __CPROVER_context_t *ctx = malloc(sizeof(*ctx));
  __CPROVER_assume(ctx);
  ctx->assume = assume;

  ctx->is_fresh_seen = malloc(__CPROVER_max_symex_objects() * sizeof(bool));
  __CPROVER_assume(ctx->is_fresh_seen);
  __CPROVER_array_set(ctx->is_fresh_seen, false);

  ctx->is_fresh_size = malloc(__CPROVER_max_symex_objects() * sizeof(__CPROVER_size_t));
  __CPROVER_assume(ctx->is_fresh_size);
  __CPROVER_array_set(ctx->is_fresh_size, 0);

  ctx->is_fresh_ptr = malloc(__CPROVER_max_symex_objects() * sizeof(void *));
  __CPROVER_assume(ctx->is_fresh_ptr);
  __CPROVER_array_set(ctx->is_fresh_ptr, NULL);

  ctx->nof_fresh = 0;
  return ctx;
}

/// @brief Library implementation of the __is_fresh predicate
/// @param ptr target pointer
/// @param size size of the allocation
/// @param ctx context tracking object
/// @return true iff the pointer is fresh and of the right size
bool __is_fresh(void **ptr, __CPROVER_size_t size, __CPROVER_context_t *ctx) {
  if (ctx->assume) {
    // assumption context
    if (nondet_bool()) {
      void *result = malloc(size);
      __CPROVER_assume(result);
      ctx->is_fresh_seen[__CPROVER_POINTER_OBJECT(result)] = true;
      ctx->is_fresh_size[ctx->nof_fresh] = size;
      ctx->is_fresh_ptr[ctx->nof_fresh] = result;
      ctx->nof_fresh++;
      *ptr = result;
      return true;
    }
    return false;
  } else {
    // assertion context
    void *__ptr = *ptr;
    __CPROVER_size_t object_id = __CPROVER_POINTER_OBJECT(__ptr);
    bool seen = ctx->is_fresh_seen[object_id];
    bool r_ok = __CPROVER_r_ok(__ptr, size);
    if (!seen && r_ok) {
      ctx->is_fresh_seen[object_id] = true;
      return true;
    } else {
      return false;
    }
  }
}

/// @brief Library implementation of the __null_or_seen predicate
/// @param ptr target pointer
/// @param ctx context tracking object
/// @return true iff the pointer is null or was already seen by is_fresh
bool __null_or_seen(void **ptr, __CPROVER_context_t *ctx) {
  if (ctx->assume) {
    if (nondet_bool()) {
      *ptr = NULL;
      if (ctx->nof_fresh > 0 && nondet_bool()) {
        // fetch an already seen object nondeterministically
        __CPROVER_size_t idx = nondet_size_t();
        __CPROVER_assume(idx < ctx->nof_fresh);
        *ptr = ctx->is_fresh_ptr[idx];
      }
      return true;
    }
    return false;
  } else {
    // assertion context
    return (__pointer_equals(ptr, NULL, ctx) ||
            ctx->is_fresh_seen[__CPROVER_POINTER_OBJECT(*ptr)]);
  }
}

/// @brief Library implementation of the `ptr1 == ptr2` predicate.
/// Behaves like a nondeterministic assignment `*ptr1 = ptr2` in assumption
/// mode.
/// @param ptr1 target pointer
/// @param ptr2 second pointer
/// @param ctx context tracking struct
/// @return true iff `*ptr1 == ptr2`
bool __pointer_equals(void **ptr1, void *ptr2, __CPROVER_context_t *ctx) {
  if (ctx->assume) {
    // decide if we satisfy the predicate or not
    if (nondet_bool()) {
      *ptr1 = ptr2;
      return true;
    } else {
      return false;
    }
  } else {
    return *ptr1 == ptr2;
  }
}

/// @brief Library implementation of the `ptr1 == ptr2` predicate.
/// Behaves like a nondeterministic assignment `*ptr1 = ptr2` in assumption
/// mode.
/// @param ptr1 target pointer
/// @param ptr2 second pointer
/// @param ctx context tracking struct
/// @return true iff `*ptr1 == ptr2`
bool __pointer_in_range(void *lb, void **ptr, void *ub, __CPROVER_context_t *ctx) {
  assert(__CPROVER_r_ok(lb, 0));
  assert(__CPROVER_r_ok(ub, 0));
  assert(__CPROVER_same_object(lb, ub));
  __CPROVER_size_t lb_offset = __CPROVER_POINTER_OFFSET(lb);
  __CPROVER_size_t ub_offset = __CPROVER_POINTER_OFFSET(ub);
  assert(lb_offset <= ub_offset);

  if (ctx->assume) {
    // non-deterministically decide if the predicate must hold
    if (nondet_bool())
      return false;
    // build a nondeterministic pointer in the range [lb, ub]
    __CPROVER_size_t offset = nondet_size_t();
    __CPROVER_assume(offset <= ub_offset - lb_offset);
    *ptr = (char *)lb + offset;
    return true;
  } else {
    void *__ptr = *ptr;
    __CPROVER_size_t offset = __CPROVER_POINTER_OFFSET(__ptr);
    // check if the pointer is in range
    return __CPROVER_same_object(lb, __ptr) && lb_offset <= offset &&
           offset <= ub_offset;
  }
}

int nondet_int();

/// @brief  Implementation of __CPROVER_assignable_int
/// @param ptr target int pointer
/// @param ctx context tracking instance
/// @param write_set write set
/// @return true iff the target pointer is assignable
bool __assignable_int(int *ptr, __CPROVER_context_t *ctx,
                      __CPROVER_contracts_write_set_ptr_t write_set) {
  bool result = true;
  if (ctx->assume) {
    // in assumption mode, add this location to write set
    __CPROVER_contracts_write_set_append_assignable(write_set, ptr,
                                                    sizeof(int));
  } else {
    // in assertion mode, check if this location is in the write set
    result = __CPROVER_contracts_write_set_check_assignment(write_set, ptr,
                                                            sizeof(int));
    // prove inclusion
    __CPROVER_assert(result, "write set inclusion check");
    // havoc the location
    *ptr = nondet_int();
  }
  return result;
}

#endif //__CPROVER_pointer_predicates_defined
