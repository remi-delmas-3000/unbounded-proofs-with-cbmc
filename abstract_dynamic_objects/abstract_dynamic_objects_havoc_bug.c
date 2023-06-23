#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

typedef struct list_s {
  int val;
  struct list_s *next;
} list_t;

bool nondet_bool();
int nondet_int();

#define AO_0 &obj_0
#define AO_1                                                                   \
  (nondet_bool()                                                               \
       ? &obj_1_1                                                              \
       : (nondet_bool() ? &obj_1_2 : (nondet_bool() ? &obj_1_3 : &obj_1_4)))

#define BUG 2
#if BUG == 1
#define AO_1_BUG                                                               \
  (nondet_bool()                                                               \
       ? &obj_1_1                                                              \
       : (nondet_bool() ? &obj_1_2 : (nondet_bool() ? &obj_1_3 : &obj_1_4)))
#elif BUG == 2
#define AO_1_BUG                                                               \
  (nondet_bool()                                                               \
       ? &obj_1_2                                                              \
       : (nondet_bool() ? &obj_1_1 : (nondet_bool() ? &obj_1_3 : &obj_1_4)))
#elif BUG == 3
#define AO_1_BUG                                                               \
  (nondet_bool()                                                               \
       ? &obj_1_3                                                              \
       : (nondet_bool() ? &obj_1_2 : (nondet_bool() ? &obj_1_1 : &obj_1_4)))
#else
#define AO_1_BUG                                                               \
  (nondet_bool()                                                               \
       ? &obj_1_4                                                              \
       : (nondet_bool() ? &obj_1_2 : (nondet_bool() ? &obj_1_3 : &obj_1_1)))
#endif

list_t obj_0;

list_t obj_1_1;
list_t obj_1_2;
list_t obj_1_3;
list_t obj_1_4;

int main() {
  list_t *p = NULL;
  list_t *list = AO_0;
  list_t *tail = list;

  *list = (list_t){.next = NULL, .val = 10};

  // heap invariant: the objects form cyclic or acyclic lists
  obj_1_1.next = (nondet_bool() ? NULL : AO_1_BUG);
  obj_1_2.next = (nondet_bool() ? NULL : AO_1);
  obj_1_3.next = (nondet_bool() ? NULL : AO_1);
  obj_1_4.next = (nondet_bool() ? NULL : AO_1);

  if (nondet_bool()) {
    p = AO_1;
    // model a fresh object (i.e. distinct from the loopback object)
    list_t p_old = *p;
    list_t obj_0_old = obj_0;
    list_t obj_1_1_old = obj_1_1;
    list_t obj_1_2_old = obj_1_2;
    list_t obj_1_3_old = obj_1_3;
    list_t obj_1_4_old = obj_1_4;

    __CPROVER_havoc_object(p);

    // these are expected to pass showing that objects not pointed by p are
    // unaffected
    if (p != &obj_0) {
      assert(obj_0.val == obj_0_old.val);
      assert(obj_0.next == obj_0_old.next);
    }

    if (p != &obj_1_1) {
      assert(obj_1_1.val == obj_1_1_old.val);
      assert(obj_1_1.next == obj_1_1_old.next);
    }

    if (p != &obj_1_2) {
      assert(obj_1_2.val == obj_1_2_old.val);
      assert(obj_1_2.next == obj_1_2_old.next);
    }

    if (p != &obj_1_3) {
      assert(obj_1_3.val == obj_1_3_old.val);
      assert(obj_1_3.next == obj_1_3_old.next);
    }
    if (p != &obj_1_4) {
      assert(obj_1_4.val == obj_1_4_old.val);
      assert(obj_1_4.next == obj_1_4_old.next);
    }

    *p = (list_t){.next = NULL, .val = nondet_int()};
    tail->next = p;
    tail = p;
  END_LOOP:;

    // heap invariant for the first loop: the objects form list segments or even
    // circular structures that abstract longer structures
    list_t obj_1_1_witness3 = obj_1_1;
    list_t obj_1_2_witness3 = obj_1_2;
    list_t obj_1_3_witness3 = obj_1_3;
    list_t obj_1_4_witness3 = obj_1_4;

    assert(obj_1_1.next == &obj_1_1 || obj_1_1.next == &obj_1_2 ||
           obj_1_1.next == &obj_1_3 || obj_1_1.next == &obj_1_4 ||
           obj_1_1.next == NULL);

    assert(obj_1_2.next == &obj_1_1 || obj_1_2.next == &obj_1_2 ||
           obj_1_2.next == &obj_1_3 || obj_1_2.next == &obj_1_4 ||
           obj_1_2.next == NULL);

    assert(obj_1_3.next == &obj_1_1 || obj_1_3.next == &obj_1_2 ||
           obj_1_3.next == &obj_1_3 || obj_1_3.next == &obj_1_4 ||
           obj_1_3.next == NULL);

    assert(obj_1_4.next == &obj_1_1 || obj_1_4.next == &obj_1_2 ||
           obj_1_4.next == &obj_1_3 || obj_1_4.next == &obj_1_4 ||
           obj_1_4.next == NULL);
  }
}
