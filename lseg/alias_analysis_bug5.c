#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

typedef struct list_s {
  int value;
  struct list_s *next;
} list_t;

// let X be an abstract object representing lseg(x, NULL)
// let Y be an abstract object representing lseg(y, NULL)
void list_append_points_to(list_t *x, list_t *y) {
  // VS(X.next) = {NULL, &X}
  // VS(Y.next) = {NULL, &Y}
  // VS(x) = {&X}
  // VS(x->next)= {NULL, &X}
  // VS(y) = {&Y}
  if (!x->next) {
    // VS(X.next) = {NULL, &X}
    // VS(Y.next) = {NULL, &Y}
    // VS(x) = {&X}
    // VS(x->next)= {NULL}
    // VS(y) = {&Y}

    x->next = y;
    // VS(X.next) = {NULL, &X, &Y}
    // VS(Y.next) = {NULL, &Y}
    // VS(x) = {&Y}
    // VS(x->next)= {&Y}
    // VS(y) = {&Y}
    return;
  }

  // VS(X.next) = {NULL, &X}
  // VS(Y.next) = {NULL, &Y}
  // VS(x) = {&X}
  // VS(x->next)= {&X}
  // VS(y) = {&Y}

  list_t *second = x->next->next;

  // VS(X.next) = {NULL, &X}
  // VS(Y.next) = {NULL, &Y}
  // VS(x) = {&X}
  // VS(x->next)= {&X}
  // VS(x->next->next) = {NULL, &X}
  // VS(y) = {&Y}
  // VS(second) = {NULL, &X}

  // VS(X.next) = {NULL, &X}
  // VS(Y.next) = {NULL, &Y}
  // VS(x) = {&X}
  // VS(x->next)= {&X}
  // VS(x->next->next) = {NULL, &X}
  // VS(y) = {&Y}
  // VS(second) = {NULL, &X}

  list_t *tail = x->next;
  // VS(X.next) = {NULL, &X}
  // VS(Y.next) = {NULL, &Y}
  // VS(x) = {&X}
  // VS(x->next)= {&X}
  // VS(x->next->next) = {NULL, &X}
  // VS(y) = {&Y}
  // VS(second) = {NULL, &X}
  // VS(tail) = {&X}
  // VS(tail->next) = {NULL, &X}

  while (tail->next)
  // loop fixpoint
  // VS(X.next) = {NULL, &X}
  // VS(Y.next) = {NULL, &Y}
  // VS(x) = {&X}
  // VS(x->next)= {&X}
  // VS(x->next->next) = {NULL, &X}
  // VS(y) = {&Y}
  // VS(second) = {NULL, &X}
  // VS(tail) = {&X}
  // VS(tail->next) = {NULL, &X}
  {
    // VS(X.next) = {NULL, &X}
    // VS(Y.next) = {NULL, &Y}
    // VS(x) = {&X}
    // VS(x->next)= {&X}
    // VS(x->next->next) = {NULL, &X}
    // VS(y) = {&Y}
    // VS(second) = {NULL, &X}
    // VS(tail) = {&X}
    // VS(tail->next) = {&X}

    tail = tail->next;

    // VS(X.next) = {NULL, &X}
    // VS(Y.next) = {NULL, &Y}
    // VS(x) = {&X}
    // VS(x->next)= {&X}
    // VS(x->next->next) = {NULL, &X}
    // VS(y) = {&Y}
    // VS(second) = {NULL, &X}
    // VS(tail) = {&X}
    // VS(tail->next) = {NULL, &X}

    if (tail == second && nondet_bool()) {
      __CPROVER_assert(false, "bug5");
    }
  }

  // VS(X.next) = {NULL, &X}
  // VS(Y.next) = {NULL, &Y}
  // VS(x) = {&X}
  // VS(x->next)= {&X}
  // VS(x->next->next) = {NULL, &X}
  // VS(y) = {&Y}
  // VS(second) = {NULL, &X}
  // VS(tail) = {&X}
  // VS(tail->next) = {NULL}

  tail->next = y;

  // VS(X.next) = {NULL, &X, &Y}
  // VS(Y.next) = {NULL, &Y}
  // VS(x) = {&X}
  // VS(x->next)= {&X, &Y}
  // VS(x->next->next) = {NULL, &X, &Y}
  // VS(y) = {&Y}
  // VS(second) = {NULL, &X}
  // VS(tail) = {&X}
  // VS(tail->next) = {&Y}
}

// let X be an abstract object representing lseg(x, NULL)
// let Y be an abstract object representing lseg(y, NULL)
void list_append(list_t *x, list_t *y) {
  if (!x->next) {
    x->next = y;
    return;
  }

  list_t *second = x->next->next;
  list_t *tail = x->next;

  while (tail->next)
  // loop fixpoint
  {
    tail = tail->next;
    if (tail == second && nondet_bool()) {
      assert(false);
    }
  }
  tail->next = y;
}
