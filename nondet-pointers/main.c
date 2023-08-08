#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

typedef struct list_s {
  int value;
  struct list_s *next;
} list_t;

list_t *nondet_list_t();

int main() {
  list_t x1, x2, x3;
  // summon nondet pointer
  list_t *x = nondet_list_t();
  list_t *addr_of_y;
  list_t *addr_of_z;
  {
    list_t y;
    list_t z;
    addr_of_y = &y;
    addr_of_z = &z;
    // y and z are dead after this block
  }
  // rules out null pointers with any offset
  __CPROVER_assume(__CPROVER_POINTER_OBJECT(x) !=
                   __CPROVER_POINTER_OBJECT(NULL));

  // rules out dead objects
  __CPROVER_assume(
      __CPROVER_POINTER_OBJECT(x) !=
      __CPROVER_POINTER_OBJECT(__CPROVER_ID "__CPROVER_dead_object"));

  // rules out OOB
  __CPROVER_assume(__CPROVER_POINTER_OFFSET(x) < __CPROVER_OBJECT_SIZE(x));
  // adding this one causes vacuity
  // __CPROVER_assume(__CPROVER_POINTER_OFFSET(x) + sizeof(list_t) < __CPROVER_OBJECT_SIZE(x));

  // rules out invalid pointers
  __CPROVER_assume(!__CPROVER_is_invalid_pointer(x));

  // check that dead objects are impossible
  assert(x != addr_of_z); // fails
  assert(x != addr_of_y); // fails

  // dereference checks include
  // bounds check, null check and invalid objects check
  *x; // passes

  // fails with x = INVALID-7
  assert(x == &x1 || x == &x2 || x == &x3);

  if (x == &x1 || x == &x2 || x == &x3) {
    // this branch should be reachable but isn't
    assert(false); // passes unexpectedly
  }
}
