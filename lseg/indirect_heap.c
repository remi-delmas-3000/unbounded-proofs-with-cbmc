#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

/*
  An alternate heap model where a layer of indirection is added between
  pointers of the user program and the actual heap.

  The pointers manipulated by the user program are all dummy pointers pointing
  to dummy objects of size 0.

  These dummy pointers can be copied, we can perform arithmetic on them, but
  they cannot be dereferenced directly because of the size 0.

  The dummy pointers are used as indices into the heap model.

  The heap model maps dummy pointers to either _real objects_ or _assumptions_.

  When a dummy pointer does not have a corresponding real object in the heap model,
  we say it is opaque.

  The only action that can be done with an opaque pointer is to query the
  existence of an assumption for it.

  An assumption about an opaque pointer describes the properties it would have
  if it were real.

  We can turn an assumption into real objects by unwinding the assumption,
  Unwinding creates new real objects, new constraints and new opaque pointers
  and assumptions.

  This indirection layer between the user program and the
  heap allows modelling unbounded heaps using inductively
  defined assumptions, unwinding assumptions dynamically
  and checking inductively defined assertions as well.

  This enables unbounded proofs through inductive reasoning. 
*/

extern __CPROVER_size_t __CPROVER_max_malloc_size;
int __builtin_clzll(unsigned long long);
int nondet_int();

// Maximum number of objects that can exist in CBMC's symex.
#define __CPROVER_max_symex_objects                                            \
  (1ULL << __builtin_clzll(__CPROVER_max_malloc_size))

typedef struct list_s {
  int value;
  struct list_s *next;
} list_t;

// assumption that there is a list segment between dummy pointers x and y
typedef struct {
  void *x;
  void *y;
} __lseg_t;

// map from dummy pointer IDs to assumptions
__lseg_t *__lseg;
void __lseg_init() {
  __lseg = __CPROVER_allocate(__CPROVER_max_symex_objects * sizeof(*__lseg), 1);
  __CPROVER_array_set(__lseg, (__lseg_t){.x = NULL, .y = NULL});
}

// true if the dummy pointer is pointing to an opaque object (to a real object
// otherwise)
bool *__opaque;

void __opaque_init() {
  __opaque =
      __CPROVER_allocate(__CPROVER_max_symex_objects * sizeof(*__opaque), 1);
  __CPROVER_array_set(__opaque, true);
}

// true if the dummy pointer is pointing to a live object
bool *__live;

void __live_init() {
  __live = __CPROVER_allocate(__CPROVER_max_symex_objects * sizeof(*__live), 1);
  __CPROVER_array_set(__live, false);
}

// map from dummy object IDs to base pointer of real object.
void **__real_base;

void __real_base_init() {
  __real_base = __CPROVER_allocate(
      __CPROVER_max_symex_objects * sizeof(*__real_base), 1);
  __CPROVER_array_set(__real_base, false);
}

// __summons a fresh dummy pointer to make it ready to receive an assumption or a
// real object
void *__summon() { return malloc(0); }

void *__malloc(size_t size) {
  void *dummy = __summon();
  void *real = malloc(size);
  size_t id = __CPROVER_POINTER_OBJECT(dummy);
  __real_base[id] = real;
  __opaque[id] = false;
  __live[id] = true;
  return dummy;
}

void __free(void *dummy) {
  __CPROVER_precondition(__live[__CPROVER_POINTER_OBJECT(dummy)], "freeing live object");
  size_t id = __CPROVER_POINTER_OBJECT(dummy);
  free(dummy);
  if (__opaque[id]) {
    __lseg[id] = (__lseg_t){.x = NULL, .y = NULL};
  } else {
    free(__real_base[id]);
    __real_base[id] = NULL;
  }
  __opaque[id] = true;
  __live[id] = false;
}

// translates a dummy pointer into a pointer to real object
void *__translate(void *dummy) {
  __CPROVER_precondition(!__opaque[__CPROVER_POINTER_OBJECT(dummy)],
                         "object is real");
  return __real_base[__CPROVER_POINTER_OBJECT(dummy)] + __CPROVER_POINTER_OFFSET(dummy);
}

// posts an lseg(x, y) assumption
void __assume_lseg(list_t *dummy_x, list_t *dummy_y) {
  size_t id = __CPROVER_POINTER_OBJECT(dummy_x);
  __real_base[id] = NULL;
  __opaque[id] = true;
  __live[id] = true;
  __lseg[id] = (__lseg_t){.x = dummy_x, .y = dummy_y};
}

// checks if an lseg(dummy_x, dummy_y) assumption exists and unfolds it
void __unwind_lseg(void *dummy_x, void *dummy_y) {
  __CPROVER_precondition(__opaque[__CPROVER_POINTER_OBJECT(dummy_x)],
                         "object is opaque");
  __CPROVER_precondition(
      __lseg[__CPROVER_POINTER_OBJECT(dummy_x)].x == dummy_x &&
          __lseg[__CPROVER_POINTER_OBJECT(dummy_x)].y == dummy_y,
      "lseg(x, y) assumption found");
  size_t id = __CPROVER_POINTER_OBJECT(dummy_x);
  // create a real object for dummy_x
  list_t *real = malloc(sizeof(list_t));
  __real_base[id] = real;
  __opaque[id] = false;
  __lseg[id] = (__lseg_t){.x = NULL, .y = NULL};

  // the terminal case
  real->next = dummy_y;

  // the inductive case
  if (nondet_int()) {
    real->next = __summon();
    __assume_lseg(real->next, dummy_y);
  }
}

// recursively evaluates lseg(x, y) ignoring separation constraints for now
bool __eval_lseg(list_t *dummy_x, list_t *dummy_y, size_t lh) {
  __CPROVER_precondition(lh > 0, "max recursion depth");
  if (lh == 0)
  {
    // max depth reached, fail
    return false;
  }
  if (__opaque[__CPROVER_POINTER_OBJECT(dummy_x)]) {
    __lseg_t a = __lseg[__CPROVER_POINTER_OBJECT(dummy_x)];
    // the assumption is for a different pointer, fail
    if (a.x != dummy_x)
      return false;
    // found assumption lseg(dummy_x, dummy_y), succeed
    if (a.y == dummy_y)
      return true;
    // found assumption for another tail pointer
    // try evaluating lseg(dummy_x, dummy_tail)
    return __eval_lseg(a.y, dummy_y, lh - 1);
  } else {
    // found a real object, evaluate recursively
    list_t *real_x = (list_t *)__translate(dummy_x);
    if (real_x->next == dummy_y)
      return true;
    return __eval_lseg(real_x->next, dummy_y, lh - 1);
  }
}

// __translate program
void list_append(list_t *x, list_t *y) {
  __unwind_lseg(x, NULL);

  if (((list_t *)__translate(x))->next == NULL) {
    ((list_t *)__translate(x))->next = y;
    // check post condition on exit
    assert(__eval_lseg(y, NULL, 1));
    assert(__eval_lseg(x, y, 1));
    return;
  }

  list_t *tail = ((list_t *)__translate(x))->next;

  // loop invariant base case
  assert(__eval_lseg(x, tail, 1));
  assert(__eval_lseg(tail, NULL, 1));

  // loopback update
  if (nondet_int()) {
    // summon fresh tail pointer
    // and assume loop invariant between x and tail
    tail = __summon();
    __assume_lseg(x, tail);
    __assume_lseg(tail, NULL);
    // sanity check the invariant holds
    assert(__eval_lseg(x, tail, 1));
    assert(__eval_lseg(tail, NULL, 1));
  }

  // sanity check the invariant holds coming both from base and step case
  assert(__eval_lseg(x, tail, 1));
  assert(__eval_lseg(tail, NULL, 1));

  // unwind tail assumption
  __unwind_lseg(tail, NULL);

  // sanity check the invariant still holds after unwinding
  assert(__eval_lseg(x, tail, 2));
  assert(__eval_lseg(tail, NULL, 2));

  if (((list_t *)__translate(tail))->next != NULL) {
    tail = ((list_t *)__translate(tail))->next;

    // loop invariant
    assert(__eval_lseg(x, tail, 2));
    assert(__eval_lseg(tail, NULL, 1));
    __CPROVER_assume(false);
  }
  #ifndef BUG1
  ((list_t *)__translate(tail))->next = y;
  #endif

  #ifdef BUG2
  __unwind_lseg(y, NULL);
  ((list_t *)__translate(y))->next = tail;
  #endif

}

int main() {
  // ghost state setup
  __opaque_init();
  __live_init();
  __real_base_init();
  __lseg_init();

  // preconditions
  list_t *x = __summon();
  __assume_lseg(x, NULL);

  list_t *y = __summon();
  __assume_lseg(y, NULL);

  // call function
  list_append(x, y);

  // postconditions
  assert(__eval_lseg(x, y, 2));
  assert(__eval_lseg(y, NULL, 2));
  return 0;
}
