#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

// nondet function
int nondet_int();

// Max malloc size in CBMC
extern __CPROVER_size_t __CPROVER_max_malloc_size;

// Number of leading zeros in a long long
int __builtin_clzll(unsigned long long);

// Max number of objects that can exist in CBMC's symex as a function of
// __CPROVER_max_malloc_size.
#define __CPROVER_max_symex_objects                                            \
  (1ULL << __builtin_clzll(__CPROVER_max_malloc_size))

// True iff the object `i` is a proxy object.
bool *__is_proxy;

void __is_proxy_init() {
  __is_proxy =
      __CPROVER_allocate(__CPROVER_max_symex_objects * sizeof(*__is_proxy), 1);
  __CPROVER_array_set(__is_proxy, false);
}

// True iff the proxy object `i` has a real object.
bool *__has_real_obj;

void __has_real_obj_init() {
  __has_real_obj = __CPROVER_allocate(
      __CPROVER_max_symex_objects * sizeof(*__has_real_obj), 1);
  __CPROVER_array_set(__has_real_obj, false);
}

// Map from proxy object IDs to base pointer of real object.
void **__real_obj;

void __real_obj_init() {
  __real_obj =
      __CPROVER_allocate(__CPROVER_max_symex_objects * sizeof(*__real_obj), 1);
  __CPROVER_array_set(__real_obj, NULL);
}

// __summons a fresh proxy pointer to make it ready to receive an assumption or
// a real object
void *__summon() {
  void *proxy = malloc(0);
  __CPROVER_assume(proxy);
  size_t proxy_id = __CPROVER_POINTER_OBJECT(proxy);
  __is_proxy[proxy_id] = true;
  __has_real_obj[proxy_id] = false;
  return proxy;
}

// rebases a non-null prox pointer into a pointer to real object
void *__rebase(void *ptr) {
  __CPROVER_precondition(ptr, "rebased pointer not null");
  __CPROVER_precondition(__is_proxy[__CPROVER_POINTER_OBJECT(ptr)],
                         "x is proxy");
  __CPROVER_precondition(__has_real_obj[__CPROVER_POINTER_OBJECT(ptr)],
                         "x has real");
  return __real_obj[__CPROVER_POINTER_OBJECT(ptr)] +
         __CPROVER_POINTER_OFFSET(ptr);
}

void *__lift(void *real) {
  size_t real_offset = __CPROVER_POINTER_OFFSET(real);
  __is_proxy[__CPROVER_POINTER_OBJECT(real)] = false;
  // base pointer for the real objet
  void *real_base = real - real_offset;
  void *proxy = __summon();
  size_t proxy_id = __CPROVER_POINTER_OBJECT(proxy);
  __is_proxy[proxy_id] = true;
  __has_real_obj[proxy_id] = true;
  __real_obj[proxy_id] = real_base;
  return proxy + real_offset;
}

void *__malloc(size_t size) {
  void *proxy = __summon();
  void *real = malloc(size);
  __is_proxy[__CPROVER_POINTER_OBJECT(real)] = false;
  size_t proxy_id = __CPROVER_POINTER_OBJECT(proxy);
  __has_real_obj[proxy_id] = true;
  __real_obj[proxy_id] = real;
  return proxy;
}

void __free(void *proxy) {
  __CPROVER_precondition(__is_proxy[__CPROVER_POINTER_OBJECT(proxy)],
                         "is proxy");
  __CPROVER_precondition(__has_real_obj[__CPROVER_POINTER_OBJECT(proxy)],
                         "has real");
  size_t proxy_id = __CPROVER_POINTER_OBJECT(proxy);
  void *real_obj = __real_obj[proxy_id];
  free(proxy);
  free(real_obj);
  __is_proxy[proxy_id] = false;
  __has_real_obj[proxy_id] = false;
  __real_obj[proxy_id] = NULL;
}

// Singly linked list.
typedef struct list_s {
  int value;
  struct list_s *next;
} list_t;

// Assumption that there is a list segment between proxy pointers x and y
typedef struct {
  void *x;
  void *y;
} __lseg_t;

// initialise assumptions map
void __lseg_init();

// gets the assumption for x
__lseg_t __get_lseg(list_t *x);

// sets an assumption for x
void __set_lseg(list_t *x, __lseg_t a);

#ifdef SHADOW_MAP
// byte level assumption map (blows up)
#include "shadow_map.h"
shadow_map_t __lseg;
void __lseg_init() {
  // store a shadow __lseg_t struct for each pointer
  shadow_map_init(&__lseg, sizeof(__lseg_t));
}

__lseg_t __get_lseg(list_t *x) { return *((__lseg_t *)shadow_map_get(&__lseg, x)); }

void __set_lseg(list_t *x, __lseg_t a) {
  *((__lseg_t *)shadow_map_get(&__lseg, x)) = a;
}

#else
// object level assumption map (will not work for list nodes embedded in structs
// alongside other members).
__lseg_t *__lseg;

void __lseg_init() {
  __lseg = __CPROVER_allocate(__CPROVER_max_symex_objects * sizeof(*__lseg), 1);
  __CPROVER_array_set(__lseg, (__lseg_t){.x = NULL, .y = NULL});
}

__lseg_t __get_lseg(list_t *x) {
  return __lseg[__CPROVER_POINTER_OBJECT(x)];
}
void __set_lseg(list_t *x, __lseg_t a) {
  __lseg[__CPROVER_POINTER_OBJECT(x)] = a;
}
#endif

// posts an lseg(x, y) assumption
void __assume_lseg(list_t *proxy_x, list_t *proxy_y) {
  __CPROVER_precondition(__is_proxy[__CPROVER_POINTER_OBJECT(proxy_x)],
                         "x is proxy");
  __CPROVER_precondition(
      proxy_y ==> __is_proxy[__CPROVER_POINTER_OBJECT(proxy_y)], "y is proxy");
  size_t id = __CPROVER_POINTER_OBJECT(proxy_x);
  __has_real_obj[id] = false;
  __real_obj[id] = NULL;
  __set_lseg(proxy_x, (__lseg_t){.x = proxy_x, .y = proxy_y});
}

// unwinds the predicate definition for k steps, emits an assumption at k == 0
void __unwind_lseg_rec(list_t *proxy_x, list_t *proxy_y, size_t k) {
  if (k == 0) {
    __assume_lseg(proxy_x, proxy_y);
  } else {
    size_t proxy_id = __CPROVER_POINTER_OBJECT(proxy_x);
    // is_fresh(x, sizeof(*x))
    list_t *real = malloc(sizeof(list_t));
    __has_real_obj[proxy_id] = true;
    __real_obj[proxy_id] = real;
    __set_lseg(proxy_x, (__lseg_t){.x = NULL, .y = NULL});
    if (nondet_int()) {
      // the terminal case
      real->next = proxy_y;
    } else {
      // recursive case
      real->next = __summon();
      __unwind_lseg_rec(real->next, proxy_y, k - 1);
    }
  }
}

// checks that an lseg(proxy_x, proxy_y) assumption exists and unwinds k steps
void __unwind_lseg(list_t *proxy_x, list_t *proxy_y, size_t k) {
  __CPROVER_precondition(__is_proxy[__CPROVER_POINTER_OBJECT(proxy_x)],
                         "x is proxy");
  __CPROVER_precondition(
      proxy_y ==> __is_proxy[__CPROVER_POINTER_OBJECT(proxy_x)], "y is proxy");
  __CPROVER_precondition(
      __get_lseg(proxy_x).x == proxy_x && __get_lseg(proxy_x).y == proxy_y,
      "lseg(x, y) assumption found");
  __unwind_lseg_rec(proxy_x, proxy_y, k);
}

// recursively evaluates lseg(x, y) ignoring separation constraints for now
bool __eval_lseg(list_t *proxy_x, list_t *proxy_y, size_t k) {
  __CPROVER_precondition(__is_proxy[__CPROVER_POINTER_OBJECT(proxy_x)],
                         "x is proxy");
  __CPROVER_precondition(
      proxy_y ==> __is_proxy[__CPROVER_POINTER_OBJECT(proxy_y)], "y is proxy");
  __CPROVER_precondition(k > 0, "max recursion depth");
  if (k == 0) {
    // max depth reached, fail
    return false;
  }
  if (__has_real_obj[__CPROVER_POINTER_OBJECT(proxy_x)]) {
    // evaluate recursively on the real object
    list_t *real_x = (list_t *)__rebase(proxy_x);
    if (real_x->next == proxy_y /* (list_t *)__rebase(proxy_y) */) {
      return true;
    }
    return __eval_lseg(real_x->next, proxy_y, k - 1);
  } else {
    // look for an assumption
    __lseg_t a = __get_lseg(proxy_x);
    // the assumption is for a pointer with different offset, fail
    if (a.x != proxy_x)
      return false;
    // found assumption lseg(proxy_x, proxy_y), succeed
    if (a.y == proxy_y)
      return true;
    // found assumption for another tail pointer
    // try evaluating recursively for lseg(proxy_x, tail)
    return __eval_lseg(a.y, proxy_y, k - 1);
  }
}

// rewritten program program
void list_append(list_t *x, list_t *y) {

  if (((list_t *)__rebase(x))->next == NULL) {
    ((list_t *)__rebase(x))->next = y;
    return;
  }

  list_t *second =((list_t *)__rebase(((list_t *)__rebase(x))->next))->next;
  list_t *tail = ((list_t *)__rebase(x))->next;

  // loop invariant base case
  __CPROVER_assert(__eval_lseg(x, tail, 3), "lseg(x, tail) base case");
  __CPROVER_assert(__eval_lseg(tail, NULL, 3), "lseg(tail, null) base case");

  // use the points to information to generate a nondet pointer
  // VS(tail) = { x, x->next, x->next->next, second, X }

  if (nondet_int()) {
    tail = x;
  }

  if(nondet_int()) {
    tail = ((list_t *)__rebase(x))->next;
  }

  if(nondet_int()) {
    tail = ((list_t *)__rebase(((list_t *)__rebase(x))->next))->next;
  }

  if (nondet_int()) {
    tail = __summon();
    __assume_lseg(x, tail);
    __unwind_lseg(x, tail, 1);
    __assume_lseg(tail, NULL);
    __unwind_lseg(tail, NULL, 1);
  }

  __CPROVER_assume(tail);

  if (((list_t *)__rebase(tail))->next != NULL) {
#ifdef BUG3
    if (nondet_int())
      goto LOOP_EXIT;
#endif
    tail = ((list_t *)__rebase(tail))->next;

#ifdef BUG4
    if(nondet_int())
      tail = y;
#endif

#ifdef BUG5
    if(tail == second) {
      __CPROVER_assert(false, "bug5");
    }
#endif

    // instrument step
    __CPROVER_assert(tail, "step case");
    __CPROVER_assert(__eval_lseg(x, tail, 3), "lseg(x, tail) step case");
    __CPROVER_assert(__eval_lseg(tail, NULL, 3), "lseg(tail, null) step case");
    __CPROVER_assume(false);
  }
LOOP_EXIT:;
#ifndef BUG1
  ((list_t *)__rebase(tail))->next = y;
#endif

#ifdef BUG2
  ((list_t *)__rebase(y))->next = tail;
#endif
}

int main() {
  // ghost state setup
  __is_proxy_init();
  __has_real_obj_init();
  __real_obj_init();
  __lseg_init();

  // preconditions
  list_t *x = __summon();
  __assume_lseg(x, NULL);
  __unwind_lseg(x, NULL, 3);

  list_t *y = __summon();
  __assume_lseg(y, NULL);
  __unwind_lseg(y, NULL, 1);

  // call function
  list_append(x, y);

  // // postconditions
  assert(__eval_lseg(x, y, 3));
  assert(__eval_lseg(y, NULL, 3));
  return 0;
}
