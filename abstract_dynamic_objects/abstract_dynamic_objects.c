/* Recreation of the example in "template-based verification of heap
 * manipulating programs" */

#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

/* A program with two loops.

- The first loop builds a loop-free singly-linked list of nondeterministic
length. The loop only builds nodes that have the property `10 <= node->val &&
node->val <= 20`.
- The second loop iterates through the list starting from the head node and
checks that the property `10 <= node->val && node->val <= 20` holds for each
node.
*/

typedef struct list_s {
  int val;
  struct list_s *next;
} list_t;

bool nondet_bool();
int nondet_int();

int original() {
  list_t *p = NULL;
  list_t *list = malloc(sizeof(list_t));;
  list_t *tail = list;
  *list = (list_t){.next = NULL, .val = 10};

  // builds list->p_1-> ... ->p_n->NULL
  while (nondet_bool()) {
    int x = nondet_int();
    if (!(10 <= x && x <= 20)) {
      goto LOOP_END; // continue
    }
    p = malloc(sizeof(list_t)); // AO_1
    *p = (list_t){.next = NULL, .val = x};
    tail->next = p;
    tail = p;
  LOOP_END:;
  }

  p = list;

  while (p != NULL) {
    assert((10 <= p->val && p->val <= 20));
    if (p->val < 20)
      p->val++;
    p = p->next;
  }
}

/*

To enable unbounded verification of such heap manipulating programs with
unbounded dynamic allocation, the possibly unbounded set of objects allocated
at each allocation site `i` is modelled using a single abstract object `AO_i`.

A static analysis pass is performed to determine, for each abstract object and
each program location,the set of all distinct pointers variables of the program
that can point to the abstract object. The max cardinality of this set over all
program locations defines the number of concrete objects to use to
concretize the abstract object AO_i = {o_i_1, ..., o_i_n};

Then, the original program is rewritten to a new program operating on a finite
heap as follows:
- the program is extended with new static objects representing the
concretisation of abstract objects AO_i for all i;
- each malloc call at location `i` is replaced by a nondet selection over AO_i =
{o_i_1, ..., o_i_n};

```c
type_t *ptr = malloc(sizeof(type_t));
```

becomes
```c
type_t *ptr = nondet_select(&o_i_1, ..., &o_i_n);
```
- loops are eliminated by rewriting them to conditional blocks (i.e. changing
`while` to `if`) and introducing non-deterministic loopback variables for the
variables modified by the loop.

For instance:

```
while(condition)
__CPROVER_assigns(t1, ..., tn)
__CPROVER_loop_invariant(I)
{
  body();
}
```

is rewritten to:

```
// base case invariant
assert(I);

// loopback update
if(nondet())
{
  t1_t loopback_t1 = nondet_t1_t();
  t1 = loopback_t1();
  ...
  tn_t loopback_tn = nondet_tn_t();
  tn = loopback_tn;
}

assume(I);

if(condition)
{
  body();

  // check invariant
  assert(I);
  assume(false);
}

```

The loopback variables are a nondeterministic abstraction of the values of
variables modified by the loop when reentering the loop in an arbitrary
iteration.

When these variables are pointer-typed, the default abstraction is the points-to
set computed by the static analysis pass on the original program.
For exmaple, if `points_to(p) = {&x, &AO_0, &AO_1}` in the original program
then `points_to(loopback_p) = {&x, &o_0_1, ..., &o_0_n, &o_1_1, ..., &o_1_m,}`
in the transformed program.

To prove soundness of this model we must prove that the transformed program
P_abs = (S_abs, S0_abs, T_abs) can simulate any behaviour of the original
program P = (S, S0, T).

An abstract state `p_abs` simulates a concrete state `p`, noted `p_abs ~ p` if
for any successor state `q` of `p` through some concrete program instruction
`instr`, there exists an abstract program instruction `instr_abs` that can be
taken from `p_abs` with successor state `q_abs` such that `q_abs ~ q`.
*/

/*
Phase 1: Introduce an abstract object `AO_i` set per dynamic allocation site `i`
and compute its number of concrete objects `N_i`.

An abstract object `AO_i` is just a name for the set of all objects that can
be allocted at an dynamic allocation site at some program location.

If `AO_i` not in a loop, then only one object can be produced and `N_i=1`.

If `AO_i` is in a loop, it can potentially produce more than one object.

For soundness, we must consider that `AO_i` can produce at least as many objects
as there are distinct pointer expressions that may point into
`AO_i`, at any program location.

Since the program has a finite number of program variables, that number is
finite, so at any location the program behaviour can depend at most on `N_i`
objects from `AO_i`.

To compute `N_i`, proceed as follows:
1.a Run a may-alias analysis up to a fixed-point on the
  loopy program in order to determine, at each program location
  `l \in Locs`, and for each abstract object `AO_i`, the set of pointer
  expressions `Ptrs(AO_i, l)` that may point to `AO_i`.
1.b Run a must-alias analysis to determine at each program location, which
  pointers are necessarily equal. Use the implied equivalence classes to
  quotient the sets `Ptrs(AO_i, l)` at each location resulting in the sets
  `Ptrs~(AO_i, l)` at each location.
1.c The final result `AO_i` is `N_i = Max_{l \in Locs}{|Ptrs~(AO_i, l)|}`.


Things to note that are not explained in the paper : one cannot reuse a standard
points-to analysis and must-alias analysis when abstract objects are involved.

Since the same abstract object virtually represents potentially distinct
concrete objects, knowing `points-to(p) = {AO_i} && points-to(q) = {AO_i}` is
not sufficient to derive `p == q`.

We believe that the points-to analysis is sound, but we should still try to find
a way to verify the output of the points-to analysis and cardinality computation
is correct (maybe through some BMC at least);
*/

int abstraction() {
  //--- must alias:
  // empty
  //--- points-to:
  // p ~ {}
  // p->next ~ {}
  // list ~ {}
  // list->next ~ {}
  // tail ~ {}
  // tail->next ~ {}
  //---
  // Ptrs~(AO_0) = {}
  // Ptrs~(AO_1) = {} // size 0

  list_t *p = NULL;
  list_t *list = malloc(sizeof(list_t)); // AO_0 size 1
  list_t *tail = list;
  *list = (list_t){.next = NULL, .val = 10};
  //--- must alias:
  // tail == list
  // tail->next == list->next
  //--- points-to:
  // p ~ NULL
  // p->next ~ invalid
  // list ~ AO_0
  // list->next ~ NULL
  // tail ~ AO_0
  // tail->next ~ NULL
  //---
  // Ptrs~(AO_0) = {[tail, list]}
  // Ptrs~(AO_1) = {} // size 0

  //--- must alias:
  // empty
  //--- points-to:
  // p ~ NULL, AO_1
  // p->next ~ invalid, NULL (null when p == &AO_1)
  // list ~ AO_0
  // list->next ~ NULL, AO_1
  // tail ~ AO_0, AO_1
  // tail->next ~ NULL
  //---
  // Ptrs~(AO_0) = {tail, list}
  // Ptrs~(AO_1) = {p, list->next, tail} size 3
  while (nondet_bool()) {
    int x = nondet_int();
    if (!(10 <= x && x <= 20)) {
      // this jump propagates the points-to state at the end of the loop to the
      // end of the loop
      goto LOOP_END;
    }
    p = malloc(sizeof(list_t)); // AO_1
    //--- must alias:
    // empty
    //--- points-to:
    // p ~ AO_1
    // p->next ~ invalid, NULL
    // list ~ AO_0
    // list->next ~ NULL, AO_1
    // tail ~ AO_0, AO_1
    // tail->next ~ NULL
    //---
    // Ptrs~(AO_0) = {tail, list}
    // Ptrs~(AO_1) = {p, list->next, tail} size 3

    *p = (list_t){.next = NULL, .val = x};
    //--- must alias:
    // empty
    //--- points-to:
    // p ~ AO_1
    // p->next ~ NULL
    // list ~ AO_0
    // list->next ~ NULL, AO_1
    // tail ~ AO_0, AO_1
    // tail->next ~ NULL
    //---
    // Ptrs~(AO_0) = {tail, list}
    // Ptrs~(AO_1) = {p, list->next, tail} size 3

    tail->next = p;
    // loop back
    //--- must alias:
    // tail->next == p
    //--- points-to:
    // p ~ AO_1
    // p->next ~ NULL
    // list ~ AO_0
    // list->next ~ NULL, AO_1
    // tail ~ AO_0, AO_1
    // tail->next ~ AO_1
    //---
    // Ptrs~(AO_0) = {tail, list}
    // Ptrs~(AO_1) = {[p, tail->next], list->next, tail} size 3

    tail = p;
    //--- must alias:
    // tail == p
    //--- points-to:
    // p ~ AO_1
    // p->next ~ NULL
    // list ~ AO_0
    // list->next ~ NULL, AO_1
    // tail ~ AO_1
    // tail->next ~ NULL
    //---
    // Ptrs~(AO_0) = {tail, list}
    // Ptrs~(AO_1) = {[p, tail], list->next} size 2

  LOOP_END:;
    //--- must alias:
    // empty
    //--- points-to:
    // p ~ NULL, AO_1
    // p->next ~ invalid, NULL
    // list ~ AO_0
    // list->next ~ NULL, AO_1
    // tail ~ AO_0, AO_1
    // tail->next ~ NULL
    //---
    // Ptrs~(AO_0) = {tail, list}
    // Ptrs~(AO_1) = {p, list->next, tail} size 3
  }

  p = list;
  //--- must alias:
  // p == list
  // p->next == list->next
  //--- points-to:
  // p ~ AO_0
  // p->next ~ NULL, AO_1
  // list ~ AO_0
  // list->next ~ NULL, AO_1
  // tail ~ AO_0, AO_1
  // tail->next ~ NULL
  //---
  // Ptrs~(AO_0) = {tail, [p, list]}
  // Ptrs~(AO_1) = {[p->next, list->next], tail} // size 2

  //--- must alias:
  // empty
  //--- points-to:
  // p ~ NULL, AO_0, AO_1
  // p->next ~ invalid, AO_1 // invalid when p == NULL, AO_1 when p != NULL
  // list ~ AO_0
  // list->next ~ NULL, AO_1
  // tail ~ AO_0, AO_1
  // tail->next ~ NULL
  //---
  // Ptrs~(AO_0) = {tail, list, p->next}
  // Ptrs~(AO_1) = {p, p->next, list->next, tail} size 4

  while (p != NULL) {
    //--- must alias:
    // empty
    //--- points-to:
    // p ~ AO_0, AO_1
    // p->next ~ NULL, AO_1
    // list ~ AO_0
    // list->next ~ NULL, AO_1
    // tail ~ AO_0, AO_1
    // tail->next ~ NULL
    //---
    // Ptrs~(AO_0) = {tail, [p, list]}
    // Ptrs~(AO_1) = {[p->next, list->next], tail} // size 2
    assert((10 <= p->val && p->val <= 20));
    if (p->val < 20)
      p->val++;
    p = p->next;
    //--- must alias:
    // empty
    //--- points-to:
    // p ~ NULL, AO_0, AO_1
    // p->next ~ invalid, AO_1 // invalid when p == NULL, AO_1 when p != NULL
    // list ~ AO_0
    // list->next ~ NULL, AO_1
    // tail ~ AO_0, AO_1
    // tail->next ~ NULL
    //---
    // Ptrs~(AO_0) = {tail, list, p->next}
    // Ptrs~(AO_1) = {p, p->next, list->next, tail} size 4
  }
}

/* We have now determined that `N_0 = 1` and `N_1 = 4`.
 *
 * We eliminate loops by introducing loopback pointer variables, and making
 * them range over the points to sets that we statically inferred before.
 *
 * When analysed using CBMC This model is memory safe, and the loopback value
 * sets for the first loop is proved stable. However the assertion in the second
 * loop fails, and the value set is not proved stable because `p = p->next`
 * yields an invalid pointer.
 *
 * We have to infer extra invariants on the concrete objects and their values.
 *
 */
#define AO_0 &obj_0
#define AO_1                                                                   \
  (nondet_bool()                                                               \
       ? &obj_1_1                                                              \
       : (nondet_bool() ? &obj_1_2 : (nondet_bool() ? &obj_1_3 : &obj_1_4)))

// static objects for AO_0
list_t obj_0;

// static objects for AO_1
list_t obj_1_1;
list_t obj_1_2;
list_t obj_1_3;
list_t obj_1_4;

// check with cbmc --nondet-static --pointer-check --bounds-check
int loop_elimination() {
  list_t *p = NULL;
  // prematerialisation of list_t *list = malloc(sizeof(list_t));
  list_t *list = AO_0;
  list_t *tail = list;

  *list = (list_t){.next = NULL, .val = 10};

  // loopback update
  if (nondet_bool()) {
    // p ~ NULL, AO_1
    p = (nondet_bool() ? NULL : AO_1);

    // tail ~ AO_0, AO_1
    tail = (nondet_bool() ? &obj_0 : AO_1);
  }

  // loop step
  if (nondet_bool()) {
    int x = nondet_int();
    if (!(10 <= x && x <= 20))
      goto END_LOOP;
    // prematerialisation of list_t *p = malloc(sizeof(list_t));
    p = AO_1;
    {
      // the object comes out uninitialised
      list_t nondet;
      *p = nondet;
    }
    *p = (list_t){.next = NULL, .val = x};
    tail->next = p;
    tail = p;
  END_LOOP:;
    // assert p ~ NULL, AO_1
    assert(p == NULL || p == &obj_1_1 || p == &obj_1_2 || p == &obj_1_3 ||
           p == &obj_1_4);

    // assert tail ~ AO_0, AO_1
    assert(tail == &obj_0 || tail == &obj_1_1 || tail == &obj_1_2 ||
           tail == &obj_1_3 || tail == &obj_1_4);
    __CPROVER_assume(false);
  }

  p = list;

  if (nondet_bool()) {
    // loopback update
    // p ~ NULL, AO_0, AO_1
    list_t *p_lb = (nondet_bool() ? NULL : (nondet_bool() ? AO_0 : AO_1));
    p = p_lb;
  }

  if (p != NULL) {
    assert((10 <= p->val && p->val <= 20));
    if (p->val < 20)
      p->val++;
    p = p->next;

    // assert p ~ NULL, AO_0, AO_1
    assert(p == NULL || p == &obj_0 || p == &obj_1_1 || p == &obj_1_2 ||
           p == &obj_1_3 || p == &obj_1_4);
    __CPROVER_assume(false);
  }
}

/*
  The last step is to infer missing lemmas on the finite heap that we have.

  These lemmas describe how objects point to each other to form NULL terminated
  list segments or cylcic structures.

  Without introducing cycles the abstraction would not be closed and the whole
  technique would not work.

  Open questions that are not answered in the paper:
  - How to do termination proofs on this model ? These cycles will forbid
  termination proofs since on a cycle there is no decreasing metric that we can
  check.
  - The lemmas that enforce the list segment structure are directly
  assumed in the step case of the first loop, and checked for preservation,
  but they do not seem to have a corresponding base case check.

  This would be hard to do check the base case in the transformed program since
  morally these objects only pop into existence after each new loop iteration.

  The problem with constraining all AO_0 and AO_1 objects with the invariant
  before the loop step is that the AO_1 object that will be selected in the body
  of the loop to represent the malloc'd object is already going to satisfy the
  constraints that that we want check at the end of the step (this can certainly
  be a source of unsoundness). One way to work around this would be to say that
  "the fresh object allocated from AO_1 in the body of the loop and the loopback
  from AO_1 object are different" (which models freshness and would hold in a
  real execution) an havoc the object selected in the body of the loop.

  analyse with cbmc --nondet-static --pointer-check --bounds-check
*/

int lemma_inference() {
  list_t *p = NULL;
  // prematerialisation of list_t *list = malloc(sizeof(list_t));
  list_t *list = AO_0;
  list_t *tail = list;

  *list = (list_t){.next = NULL, .val = 10};

  // check invariant in the base case
  // check p ~ NULL, AO_1
  assert(p == NULL || p == &obj_1_1 || p == &obj_1_2 || p == &obj_1_3 ||
         p == &obj_1_4);

  // check tail ~ AO_0, AO_1
  assert(tail == &obj_0 || tail == &obj_1_1 || tail == &obj_1_2 ||
         tail == &obj_1_2 || tail == &obj_1_3);

  // heap invariant for the first loop: the objects form list segments or even
  // circular structures
  obj_1_1.next = (nondet_bool() ? NULL : AO_1);
  obj_1_2.next = (nondet_bool() ? NULL : AO_1);
  obj_1_3.next = (nondet_bool() ? NULL : AO_1);
  obj_1_4.next = (nondet_bool() ? NULL : AO_1);

  // heap invariant for the first loop: values are in range
  __CPROVER_assume(10 <= obj_0.val && obj_0.val <= 20);
  __CPROVER_assume(10 <= obj_1_1.val && obj_1_1.val <= 20);
  __CPROVER_assume(10 <= obj_1_2.val && obj_1_2.val <= 20);
  __CPROVER_assume(10 <= obj_1_3.val && obj_1_3.val <= 20);
  __CPROVER_assume(10 <= obj_1_4.val && obj_1_4.val <= 20);

  // loopback update
  if (nondet_bool()) {
    // p ~ NULL, AO_1
    p = (nondet_bool() ? NULL : AO_1);

    // tail ~ AO_0, AO_1
    tail = (nondet_bool() ? &obj_0 : AO_1);
  }

  if (nondet_bool()) {
    int x = nondet_int();
    if (!(10 <= x && x <= 20))
      goto END_LOOP;
    // prematerialisation of list_t *p = malloc(sizeof(list_t));
    p = AO_1;
    {
      // the object comes out uninitialised
      list_t nondet;
      *p = nondet;
    }
    *p = (list_t){.next = NULL, .val = x};
    tail->next = p;
    tail = p;
  END_LOOP:;
    // assert p ~ NULL, AO_1
    assert(p == NULL || p == &obj_1_1 || p == &obj_1_2 || p == &obj_1_3 ||
           p == &obj_1_4);

    // assert tail ~ AO_0, AO_1
    assert(tail == &obj_0 || tail == &obj_1_1 || tail == &obj_1_2 ||
           tail == &obj_1_3 || tail == &obj_1_4);

    // heap invariant
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
    assert(10 <= obj_0.val && obj_0.val <= 20);
    assert(10 <= obj_1_1.val && obj_1_1.val <= 20);
    assert(10 <= obj_1_2.val && obj_1_2.val <= 20);
    assert(10 <= obj_1_3.val && obj_1_3.val <= 20);
    assert(10 <= obj_1_4.val && obj_1_4.val <= 20);
    __CPROVER_assume(false);
  }

  p = list;

  // base case
  // assert p ~ NULL, AO_0, AO_1
  assert(p == NULL || p == &obj_0 || p == &obj_1_1 || p == &obj_1_2 ||
         p == &obj_1_3 || p == &obj_1_4);

  if (nondet_bool()) {
    // loopback update
    // p ~ NULL, AO_0, AO_1
    list_t *p_lb = (nondet_bool() ? NULL : (nondet_bool() ? AO_0 : AO_1));
    p = p_lb;
  }


  if (p != NULL) {
    assert((10 <= p->val && p->val <= 20));
    if (p->val < 20)
      p->val++;
    p = p->next;

    // assert p ~ NULL, AO_0, AO_1
    assert(p == NULL || p == &obj_0 || p == &obj_1_1 || p == &obj_1_2 ||
           p == &obj_1_3 || p == &obj_1_4);
    __CPROVER_assume(false);
  }
}
