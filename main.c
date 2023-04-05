#include <stdlib.h>
#include <stdbool.h>
#include "pointer_predicates.h"
#include "write_set.h"

// a simple example if instrumentation

// a memory predicate
bool is_buffer(char **buf, size_t size, size_t max_size,
               __CPROVER_context_t *ctx) {
  return (0 < size && size <= max_size) && __is_fresh(buf, size, ctx);
}

// another memory predicate
bool is_size_t(size_t **ptr, __CPROVER_context_t *ctx) {
  return __is_fresh(ptr, sizeof(size_t), ctx);
}


// a replacement stub that checks pre conditions, checks write set inclusion
// and havocs the write set
void bar_replace(char *buf, size_t size, size_t *out, __CPROVER_contracts_write_set_ptr_t write_set) {
    __CPROVER_context_t *ctx = __CPROVER_context_new(false);
    assert(is_buffer(&buf, size, 100000, ctx) && is_size_t(&out, ctx));
  __CPROVER_contracts_write_set_t __ws;
  __CPROVER_contracts_write_set_ptr_t __write_set = &__ws;
  __CPROVER_contracts_write_set_create(
      __write_set /* write_set */,
      2 /* #assignable */,
      0 /* #freeable */,
      false /* assume requires */,
      false /* assert requires */,
      false /* assume ensures */,
      false /* assert ensures */,
      true /* allow_alloc */,
      true /* allow_dealloc */
    );
    __CPROVER_contracts_write_set_append_assignable(__write_set, out, sizeof(size_t));
    __CPROVER_contracts_write_set_check_assigns_clause_inclusion(write_set, __write_set);
    *((size_t *)__CPROVER_contracts_write_set_havoc_get_assignable_target(__write_set, 0)) = nondet_size_t();
}

// 98676 variables, 67585 clauses
void foo_wrapper1(char *buf, size_t size, size_t *out, __CPROVER_contracts_write_set_ptr_t write_set) {
    __CPROVER_context_t *ctx = __CPROVER_context_new(true);
    __CPROVER_assume(is_buffer(&buf, size, 100000, ctx) && is_size_t(&out, ctx));
  __CPROVER_contracts_write_set_t __ws;
  __CPROVER_contracts_write_set_ptr_t __write_set = &__ws;
  __CPROVER_contracts_write_set_create(
      __write_set /* write_set */,
      2 /* #assignable */,
      0 /* #freeable */,
      false /* assume requires */,
      false /* assert requires */,
      false /* assume ensures */,
      false /* assert ensures */,
      true /* allow_alloc */,
      true /* allow_dealloc */
    );
    __CPROVER_contracts_write_set_append_assignable(__write_set, buf, size);
    __CPROVER_contracts_write_set_append_assignable(__write_set, out, sizeof(size_t));
    foo(buf, size, out, __write_set);
}

// 98333 variables, 67188 clauses
void foo_wrapper2(char *buf, size_t size, size_t *out, __CPROVER_contracts_write_set_ptr_t write_set) {
    __CPROVER_context_t *ctx = __CPROVER_context_new(true);
    __CPROVER_assume((0 < size && size <= 100000) && __is_fresh(&buf, size, ctx) && __is_fresh(&out, sizeof(size_t), ctx));
  __CPROVER_contracts_write_set_t __ws;
  __CPROVER_contracts_write_set_ptr_t __write_set = &__ws;
  __CPROVER_contracts_write_set_create(
      __write_set /* write_set */,
      2 /* #assignable */,
      0 /* #freeable */,
      false /* assume requires */,
      false /* assert requires */,
      false /* assume ensures */,
      false /* assert ensures */,
      true /* allow_alloc */,
      true /* allow_dealloc */
    );
    __CPROVER_contracts_write_set_append_assignable(__write_set, buf, size);
    __CPROVER_contracts_write_set_append_assignable(__write_set, out, sizeof(size_t));
    foo(buf, size, out, __write_set);
}

void foo(char *buf, size_t size, size_t *out, __CPROVER_contracts_write_set_ptr_t write_set) {
    size_t i = 0;
    __CPROVER_contracts_write_set_add_decl(write_set, &i);
    bar_replace(buf, size, &i, write_set);
    __CPROVER_contracts_write_set_record_dead(write_set, &i);

}

int main() {
    char *buf;
    size_t size;
    size_t *out;
    foo_wrapper2(buf, size, out, NULL);
}