#include <stdbool.h>
#include <stdlib.h>

// memory safety of list_search with lists of at most 5 elements
typedef struct list_s {
  int value;
  struct list_s *next;
} list_t;

bool is_list(list_t *list, size_t max_len) {
  return __CPROVER_is_fresh(list, sizeof(list_t)) &&
         (max_len == 0
              ? list->next == NULL
              : (list->next == NULL || is_list(list->next, max_len - 1)));
}

const size_t MAX_LEN = 5;

bool list_search(list_t *list, int value)
    __CPROVER_requires(list == NULL || is_list(list, MAX_LEN)) {
  return list && ((list->value == value) || list_search(list->next, value));
}

// proof harness
/*
goto-cc list_search_bounded.c
goto-instrument --dfcc main --enforce-contract-rec list_search a.out b.out
cbmc --bounds-check --pointer-check --pointer-overflow-check b.out --external-sat-solver kissat
*/
void main() {
  list_t *list;
  int value;
  list_search(list, value);
}
