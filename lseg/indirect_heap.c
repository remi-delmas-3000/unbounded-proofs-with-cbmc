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

    The dummy pointers are used as indices into the actual heap model.

    The heap model contains either _real objects_, or _opaque objects_ with
   associated _assumptions_.

    An opaque object is also allocated with size 0 and its contents cannot be
   accessed.

    The only action that can be done with an opaque object is to query the
    existence of an assumption about it.

    An assumption describes the properties an opaque object would have if
    concretized into a real object.

    The concretisation consumes the assumption, creates real objects and opaque
    objects, and creates more assumptions about these opaque objects.

    Note that opaque objects and dummy objects serve different purposes:
    - dummy objects are indices into the heap model.
    - opaque objects are indices into a set of assumptions stored within the
   heap model.

    The goal of having this indirection layer between the user program and the
   heap is to allow changing the representation of the heap by adding new
   assumptions, unfolding assumptions, etc. and have these changes being
   transparent from the perspective of the user program.

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

// map from dummy object IDs to real object IDs.
void **__real_object;

void __real_object_init() {
  __real_object = __CPROVER_allocate(
      __CPROVER_max_symex_objects * sizeof(*__real_object), 1);
  __CPROVER_array_set(__real_object, false);
}

// summons a fresh dummy pointer to make it ready to receive an assumption or a
// real object
void *summon() { return malloc(0); }

void *__malloc(size_t size) {
  void *dummy = summon();
  void *real = malloc(size);
  size_t id = __CPROVER_POINTER_OBJECT(dummy);
  __real_object[id] = real;
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
    free(__real_object[id]);
    __real_object[id] = NULL;
  }
  __opaque[id] = true;
  __live[id] = false;
}

// fetches the real pointer for this dummy pointer (the object must be real)
void *fetch_real(void *dummy) {
  __CPROVER_precondition(!__opaque[__CPROVER_POINTER_OBJECT(dummy)],
                         "object is real");
  return __real_object[__CPROVER_POINTER_OBJECT(dummy)];
}

// posts an lseg(x, y) assumption
void __assume_lseg(list_t *dummy_x, list_t *dummy_y) {
  size_t id = __CPROVER_POINTER_OBJECT(dummy_x);
  __real_object[id] = NULL;
  __opaque[id] = true;
  __live[id] = true;
  __lseg[id] = (__lseg_t){.x = dummy_x, .y = dummy_y};
}

// checks if an lseg(dummy_x, dummy_y) assumption exists and unfolds it
void __unfold_lseg(void *dummy_x, void *dummy_y) {
  __CPROVER_precondition(__opaque[__CPROVER_POINTER_OBJECT(dummy_x)],
                         "object is opaque");
  __CPROVER_precondition(
      __lseg[__CPROVER_POINTER_OBJECT(dummy_x)].x == dummy_x &&
          __lseg[__CPROVER_POINTER_OBJECT(dummy_x)].y == dummy_y,
      "lseg(x, y) assumption found");
  size_t id = __CPROVER_POINTER_OBJECT(dummy_x);
  // create a real object for dummy_x
  list_t *real = malloc(sizeof(list_t));
  __real_object[id] = real;
  __opaque[id] = false;
  __lseg[id] = (__lseg_t){.x = NULL, .y = NULL};

  // the terminal case
  real->next = dummy_y;

  // the inductive case
  if (nondet_int()) {
    real->next = summon();
    __assume_lseg(real->next, dummy_y);
  }
}

// recursively evaluates lseg(x, y)
bool eval_lseg(list_t *dummy_x, list_t *dummy_y, size_t lh) {
  __CPROVER_precondition(lh > 0, "max recursion depth");
  if (lh == 0)
    return false;
  // ignoring separation constraints for now
  if (__opaque[__CPROVER_POINTER_OBJECT(dummy_x)]) {
    __lseg_t a = __lseg[__CPROVER_POINTER_OBJECT(dummy_x)];
    if (a.x != dummy_x)
      return false;
    // success if we have an assumption lseg(dummy_x, dummy_y)
    if (a.y == dummy_y)
      return true;
    // we have an assumption for another dummy tail pointer
    // try evaluating lseg(dummy_x, dummy_tail)
    return eval_lseg(a.y, dummy_y, lh - 1);
  } else {
    list_t *real_x = (list_t *)fetch_real(dummy_x);
    if (real_x->next == dummy_y)
      return true;
    return eval_lseg(real_x->next, dummy_y, lh - 1);
  }
}

// transformed program
void list_append(list_t *x, list_t *y) {
  __unfold_lseg(x, NULL);

  if (((list_t *)fetch_real(x))->next == NULL) {
    ((list_t *)fetch_real(x))->next = y;
    // check post conditions
    assert(eval_lseg(y, NULL, 1));
    assert(eval_lseg(x, y, 1));
    return;
  }

  list_t *tail = ((list_t *)fetch_real(x))->next;

  // loop invariant base case
  assert(eval_lseg(x, tail, 1));
  assert(eval_lseg(tail, NULL, 1));

  // loopback update
  if (nondet_int()) {
    __assume_lseg(tail, NULL);
    __assume_lseg(x, tail);
    assert(eval_lseg(x, tail, 1));
  }

  // sanity check
  assert(eval_lseg(x, tail, 1));

  __unfold_lseg(tail, NULL);

  // sanity check
  assert(eval_lseg(x, tail, 2));

  if (((list_t *)fetch_real(tail))->next != NULL) {
    tail = ((list_t *)fetch_real(tail))->next;

    // loop invariant
    assert(eval_lseg(x, tail, 2));
    assert(eval_lseg(tail, NULL, 1));
    __CPROVER_assume(false);
  }
  #ifndef BUG1
  ((list_t *)fetch_real(tail))->next = y;
  #endif

  #ifdef BUG2
  __unfold_lseg(y, NULL);
  ((list_t *)fetch_real(y))->next = tail;
  #endif

}

int main() {
  // ghost state setup
  __opaque_init();
  __live_init();
  __real_object_init();
  __lseg_init();

  // preconditions
  list_t *x = summon();
  __assume_lseg(x, NULL);

  list_t *y = summon();
  __assume_lseg(y, NULL);

  // call function
  list_append(x, y);

  // postconditions
  assert(eval_lseg(x, y, 2));
  assert(eval_lseg(y, NULL, 2));
  return 0;
}
