#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

#include "pointer_predicates.h"
#include "write_set.h"

//////////////// TYPE DECLARATIONS ////////////////

#define PRECONDITION(P) assert(P)
#define POSTCONDITION(P) assert(P)

/// @brief list node data type
typedef struct node_s {
  int value;
  struct node_s *prev;
  struct node_s *next;
} node_t;

/// @brief list with head and tail sentinel nodes.
typedef struct list_s {
  node_t head;
  node_t tail;
} list_t;



//////////////// POINTER PREDICATES DECLARATIONS ////////////////

// true iff `through` is a fresh node that has `from` as predecessor
// and can eventually reach `head` through `prev` links
bool __can_reach_prev(node_t **through, node_t *from, node_t *head,
                      __CPROVER_context_t *ctx,
                      __CPROVER_contracts_write_set_ptr_t __write_set,
                      size_t lh);

// true iff `through` is a fresh node that has `from` as predecessor
// and can eventually reach `tail` through `next` links
bool __can_reach_next(node_t **through, node_t *from, node_t *tail,
                      __CPROVER_context_t *ctx,
                      __CPROVER_contracts_write_set_ptr_t __write_set,
                      size_t lh);

// True iff `list` is a fresh list object and if node is either the tail node
// or some fresh node that:
// - has list.head as previous node or can reach list.head through its previous
// node
// - has list.tail as next node or can reach list.tail through its next node
//
// if is_in_list(list, &list->tail) holds then the list is well formed and
// connected.
bool __is_in_list(list_t **list, node_t **node, __CPROVER_context_t *ctx,
                  __CPROVER_contracts_write_set_ptr_t __write_set, size_t lh);

// When called in assumption mode, adds the node pointer to the write set,
// when called in assertion mode, checks if writing to the node pointer is
// allowed by the write set.
bool __assignable_node_ptr(__CPROVER_contracts_write_set_ptr_t __write_set,
                           node_t **node, __CPROVER_context_t *ctx);

// When called in assumption mode, adds the node to the write set,
// when called in assertion mode, checks if writing to the node is
// allowed by the write set.
bool __assignable_node(__CPROVER_contracts_write_set_ptr_t __write_set,
                       node_t *node, __CPROVER_context_t *ctx);

// True if may be possible to reach the tail from the head.
// list->head.next is either null or pointing to the tail node or some pointer
// to a node that may reach the tail.
// This predicate describes how `wrong` a list can be and is used as a
// precondition for functions that are meant to detect incorrect lists and
// validate correct lists.
bool __maybe_list(list_t **list, __CPROVER_context_t *ctx,
                  __CPROVER_contracts_write_set_ptr_t __write_set, size_t lh);

// true iff the through is a node that previous node `from` or some other node
// and that has as next node either NULL, or the tail, or some other node that
// may reach the tail.
bool __maybe_reach_next(node_t **through, node_t *from, node_t *tail,
                        __CPROVER_context_t *ctx,
                        __CPROVER_contracts_write_set_ptr_t __write_set,
                        size_t lh);

//////////////// CODE UNDER VERIFICATION ////////////////

/**
 * True iff the list is empty.
 */
bool list_empty(__CPROVER_contracts_write_set_ptr_t __write_set,
                const list_t *list) {
  PRECONDITION(list);
  return list->head.next == &list->tail;
}

/**
 * Checks that the prev of the next pointer of a node points to the node.
 */
// the node must be fresh, but its next and prev pointers can be either NULL,
// point to the node or point to other fresh nodes. remark: a node that points
// to itself with both next and prev would be accepted by that function
bool list_node_next_is_valid(__CPROVER_contracts_write_set_ptr_t __write_set,
                             const node_t *node) {
  return node && node->next && node->next->prev == node;
}

/**
 * Checks that the next of the prev pointer of a node points to the node.
 */
bool list_node_prev_is_valid(__CPROVER_contracts_write_set_ptr_t __write_set,
                             const node_t *node) {
  return node && node->prev && node->prev->next == node;
}

/**
 * Inserts `to_add` immediately before `before`.
 */
void list_insert_before(__CPROVER_contracts_write_set_ptr_t __write_set,
                        list_t *list, node_t *before, node_t *to_add);

// function instrumented for dynamic frame condition checking
void __list_insert_before(__CPROVER_contracts_write_set_ptr_t __write_set,
                          list_t *list, node_t *before, node_t *to_add)
// original code
// {
//     PRECONDITION(list_node_prev_is_valid(before));
//     PRECONDITION(to_add != NULL);
//     to_add->next = before;
//     to_add->prev = before->prev;
//     before->prev->next = to_add;
//     before->prev = to_add;
//     POSTCONDITION(list_node_prev_is_valid(before));
//     POSTCONDITION(list_node_prev_is_valid(to_add));
//     POSTCONDITION(list_node_next_is_valid(to_add));
//     POSTCONDITION(before->prev == to_add);
// }
{
  RECORD_DECL(list);
  RECORD_DECL(before);
  RECORD_DECL(to_add);
  PRECONDITION(list_node_prev_is_valid(__write_set, before));
  PRECONDITION(to_add != NULL);
  CHECK_ASSIGN(to_add->next);
  to_add->next = before;
  CHECK_ASSIGN(to_add->prev);
  to_add->prev = before->prev;
  CHECK_ASSIGN(before->prev->next);
  before->prev->next = to_add;
  CHECK_ASSIGN(before->prev);
  before->prev = to_add;
  POSTCONDITION(list_node_prev_is_valid(__write_set, before));
  POSTCONDITION(list_node_prev_is_valid(__write_set, to_add));
  POSTCONDITION(list_node_next_is_valid(__write_set, to_add));
  POSTCONDITION(before->prev == to_add);
  RECORD_DEAD(list);
  RECORD_DEAD(before);
  RECORD_DEAD(to_add);
}

// Verification wrapper
void list_insert_before(__CPROVER_contracts_write_set_ptr_t __write_set,
                        list_t *list, node_t *before, node_t *to_add) {

  // lookahead: 1 concrete nodes + 1 opaque node at the boundary
  size_t lh = 2;

  // assume the requires clause
  __CPROVER_context_t *ctx_requires = __CPROVER_context_new(true);

  // clang-format off
  __CPROVER_contracts_write_set_t __ws;
  __CPROVER_contracts_write_set_ptr_t __write_set = &__ws;
  __CPROVER_contracts_write_set_create(
      __write_set /* write_set */,
      4 /* #assignable */,
      0 /* #freeable */,
      false /* assume requires */,
      false /* assert requires */,
      false /* assume ensures */,
      false /* assert ensures */,
      true /* allow_alloc */,
      true /* allow_dealloc */
    );
  // clang-format on

  __CPROVER_assume(
      __is_fresh(&to_add, sizeof(*to_add), ctx_requires) &&
      __assignable_node_ptr(__write_set, &to_add->next, ctx_requires) &&
      __assignable_node_ptr(__write_set, &to_add->prev, ctx_requires));
  __CPROVER_assume(
      __is_in_list(&list, &before, ctx_requires, __write_set, lh) &&
      __assignable_node_ptr(__write_set, &before->prev->next, ctx_requires) &&
      __assignable_node_ptr(__write_set, &before->prev, ctx_requires));

  // snapshot history variables
  node_t *old_before_prev = before->prev;

  // call function under verification
  __list_insert_before(__write_set, list, before, to_add);

  // check ensures clause
  __CPROVER_context_t *ctx_ensures = __CPROVER_context_new(false);
  assert(__is_in_list(&list, &to_add, ctx_ensures, __write_set, lh + 1));
  assert(__pointer_equals(&(to_add->next), before, ctx_ensures));
  assert(__pointer_equals(&(before->prev), to_add, ctx_ensures));
  assert(__pointer_equals(&(to_add->prev), old_before_prev, ctx_ensures));
  assert(__pointer_equals(&(to_add->prev->next), to_add, ctx_ensures));
}

/**
 * Checks that a linked list satisfies double linked list connectivity
 * constraints.
 */
bool list_is_valid(__CPROVER_contracts_write_set_ptr_t __write_set,
                   const list_t *list);

// Function instrumented for dynamic frame condition checking and loop contract
bool __list_is_valid(__CPROVER_contracts_write_set_ptr_t __write_set,
                     const list_t *list)
// original code
// {
//   if (!list) {
//     return false;
//   }
//   node_t *temp = &list->head;
//   bool head_reaches_tail = false;
//   while (temp) {
//     if (temp == &list->tail) {
//       head_reaches_tail = true;
//       break;
//     } else if (!list_node_next_is_valid(temp)) {
//       return false;
//     }
//     temp = temp->next;
//   }
//   return head_reaches_tail;
// }
{
  if (!list) {
    return false;
  }

  const node_t *temp = &list->head;
  RECORD_DECL(temp);

  bool head_reaches_tail = false;
  RECORD_DECL(head_reaches_tail);

  {
    // clang-format off
    // check invariant in the base case
    __CPROVER_context_t *ctx = __CPROVER_context_new(false);
    size_t lh = 2;
    assert(
      // either NULL
      __pointer_equals(&temp, NULL, ctx)
      ||
      (
        // OR pointing to the head or some node that can reach the head
        (
          // that is the head or some fresh node from which we can reach the head
          __pointer_equals(&temp, &list->head, ctx)
          ||
          (
              __is_fresh(&temp, sizeof(*temp), ctx)
              &&
              (
                __pointer_equals(&temp->prev, &list->head, ctx) && __pointer_equals(&(&list->head)->next, temp, ctx)
                ||
                __can_reach_prev(&temp->prev, temp, &list->head, ctx, __write_set, lh)
              )
          )
        )
        &&
        ( // and that has successor that is either
          // NULL next node
          // or the tail node
          // or some fresh node that may reach the tail
             __pointer_equals(&temp->next, NULL, ctx)
          || __pointer_equals(&temp->next, &list->tail, ctx)
          || __maybe_reach_next(&temp->next, temp, &list->tail, ctx, __write_set, lh)
        )
      )
    );
    // clang-format on
  }

  // jump to arbitrary state by assuming the invariant
  {
    // clang-format off
    __CPROVER_context_t *ctx = __CPROVER_context_new(true);
    size_t lh = 2;
    __CPROVER_assume(
      // either NULL
      __pointer_equals(&temp, NULL, ctx)
      ||
      (
        // OR pointing to the head or some node that can reach the head
        (
          // that is the head or some fresh node from which we can reach the head
          __pointer_equals(&temp, &list->head, ctx)
          ||
          (
              __is_fresh(&temp, sizeof(*temp), ctx)
            && (
              __pointer_equals(&temp->prev, &list->head, ctx) && __pointer_equals(&(&list->head)->next, temp, ctx)
              ||
              __can_reach_prev(&temp->prev, temp, &list->head, ctx, __write_set, lh)
            )
          )
        )
        &&
        ( // and that has successor that is either
          // NULL next node
          // or the tail node
          // or some fresh node that may reach the tail
             __pointer_equals(&temp->next, NULL, ctx)
          || __pointer_equals(&temp->next, &list->tail, ctx)
          || __maybe_reach_next(&temp->next, temp, &list->tail, ctx, __write_set, lh)
        )
      )
    );
    head_reaches_tail = nondet_bool();
    // clang-format on
  }

  // This models the loop step from a nondet state that satisfies the invariant.
  if (temp) {
    if (temp == &list->tail) {
      CHECK_ASSIGN(head_reaches_tail);
      head_reaches_tail = true;
      {
        // prove that the list is now fully connected
        __CPROVER_context_t *ctx = __CPROVER_context_new(false);
        size_t lh = 2;
        // working around the fact that &list->tail is not an lvalue.
        node_t *tail_ptr = &list->tail;
        assert(__is_in_list(&list, &(tail_ptr), ctx, __write_set, lh));
      }
      goto LOOP_EXIT;
    } else if (!list_node_next_is_valid(__write_set, temp)) {
      return false;
    }
    CHECK_ASSIGN(temp);
    temp = temp->next;
    {
      // clang-format off
      // assert the invariant in the step case
      __CPROVER_context_t *ctx = __CPROVER_context_new(false);
      size_t lh = 2;
      assert(
        // either NULL
        __pointer_equals(&temp, NULL, ctx)
        ||
        (
          // OR pointing to the head or some node that can reach the head
          (
            // that is the head or some fresh node from which we can reach the head
            __pointer_equals(&temp, &list->head, ctx)
            ||
            (
                __is_fresh(&temp, sizeof(*temp), ctx)
                &&
                (
                  __pointer_equals(&temp->prev, &list->head, ctx) && __pointer_equals(&(&list->head)->next, temp, ctx)
                  ||
                  __can_reach_prev(&temp->prev, temp, &list->head, ctx, __write_set, lh + 1)
                )
            )
          )
          &&
          ( // and that has successor that is either
            // NULL next node
            // or the tail node
            // or some fresh node that may reach the tail
              __pointer_equals(&temp->next, NULL, ctx)
            || __pointer_equals(&temp->next, &list->tail, ctx)
            || __maybe_reach_next(&temp->next, temp, &list->tail, ctx, __write_set, lh)
          )
        )
      );
      // clang-format on
    }
    // stop progress
    __CPROVER_assume(false);
  }

LOOP_EXIT:;
  // // TODO prove the function's post condition
  // {
  //   // prove that the list is fully connected
  //   __CPROVER_context_t *ctx = __CPROVER_context_new(false);
  //   size_t lh = 2;
  //   // working around the fact that &list->tail is not an lvalue.
  //   node_t *tail_ptr = &list->tail;
  //   assert(__is_in_list(&list, &(tail_ptr), ctx, __write_set, lh));
  // }
  RECORD_DEAD(temp);
  RECORD_DEAD(head_reaches_tail);
  return head_reaches_tail;
}

// verification wrapper
bool list_is_valid(__CPROVER_contracts_write_set_ptr_t __write_set,
                   const list_t *list) {
  // lookahead: 1 concrete nodes + 1 opaque node at the boundary
  size_t lh = 2;

  // assume the requires clause
  __CPROVER_context_t *ctx_requires = __CPROVER_context_new(true);

  // clang-format off
  __CPROVER_contracts_write_set_t __ws;
  __CPROVER_contracts_write_set_ptr_t __write_set = &__ws;
  __CPROVER_contracts_write_set_create(
      __write_set /* write_set */,
      4 /* #assignable */,
      0 /* #freeable */,
      false /* assume requires */,
      false /* assert requires */,
      false /* assume ensures */,
      false /* assert ensures */,
      true /* allow_alloc */,
      true /* allow_dealloc */
    );
  __CPROVER_assume(__maybe_list(&list, ctx_requires, __write_set, lh));
  // clang-format on

  // call function under verification
  bool return_value = __list_is_valid(__write_set, list);

  // assume the requires clause
  __CPROVER_context_t *ctx_ensures = __CPROVER_context_new(false);
  // TODO prove post condition
  // assert(return_value ==>
  //        __is_in_list(&list, &list->tail, ctx_ensures, __write_set, lh));
  // return result
  return return_value;
}

/**
 * Swaps the order two nodes in the linked list.
 */
// TODO we need a pointer predicate that describes that both nodes are in the
// same list if they are the same node, then head and tail are reachable if they
// are not the same node, then either
// [head] ...       <->[a=b]<->       ... [tail]
// [head] ...     <->[a]<->[b]<->     ... [tail]
// [head] ...     <->[b]<->[a]<->     ... [tail]
// [head] ... <->[a]<-> ... <->[b]<-> ... [tail]
// [head] ... <->[b]<-> ... <->[a]<-> ... [tail]
void list_swap_nodes(__CPROVER_contracts_write_set_ptr_t __write_set, node_t *a,
                     node_t *b) {
  RECORD_DECL(a);
  RECORD_DECL(b);
  PRECONDITION(list_node_prev_is_valid(__write_set, a));
  PRECONDITION(list_node_next_is_valid(__write_set, a));
  PRECONDITION(list_node_prev_is_valid(__write_set, b));
  PRECONDITION(list_node_next_is_valid(__write_set, b));

  if (a == b) {
    return;
  }
  node_t tmp = *b;
  RECORD_DECL(tmp);
  CHECK_ASSIGN(a->prev->next);
  a->prev->next = b;
  CHECK_ASSIGN(a->next->prev);
  a->next->prev = b;
  CHECK_ASSIGN(tmp.prev->next);
  tmp.prev->next = a;
  CHECK_ASSIGN(tmp.next->prev);
  tmp.next->prev = a;
  CHECK_ASSIGN(tmp);
  tmp = *a;
  CHECK_ASSIGN(*a);
  *a = *b;
  CHECK_ASSIGN(*b);
  *b = tmp;
  POSTCONDITION(list_node_prev_is_valid(__write_set, a));
  POSTCONDITION(list_node_next_is_valid(__write_set, a));
  POSTCONDITION(list_node_prev_is_valid(__write_set, b));
  POSTCONDITION(list_node_next_is_valid(__write_set, b));
  RECORD_DEAD(a);
  RECORD_DEAD(b);
}

void list_move_all_back(__CPROVER_contracts_write_set_ptr_t __write_set,
                        list_t *restrict dst, list_t *restrict src) {
  RECORD_DECL(dst);
  RECORD_DECL(src);
  PRECONDITION(list_is_valid(__write_set, src));
  PRECONDITION(list_is_valid(__write_set, dst));
  PRECONDITION(dst != src);
  if (!list_empty(__write_set, src)) {
    node_t *dst_back = dst->tail.prev;
    RECORD_DECL(dst_back);
    node_t *src_front = src->head.next;
    RECORD_DECL(src_front);
    node_t *src_back = src->tail.prev;
    RECORD_DECL(src_back);
    CHECK_ASSIGN(dst_back->next);
    dst_back->next = src_front;
    CHECK_ASSIGN(src_front->prev);
    src_front->prev = dst_back;
    CHECK_ASSIGN(dst->tail.prev);
    dst->tail.prev = src_back;
    CHECK_ASSIGN(src_back->next);
    src_back->next = &dst->tail;
    CHECK_ASSIGN(src->head.next);
    src->head.next = &src->tail;
    CHECK_ASSIGN(src->tail.prev);
    src->tail.prev = &src->head;
  }
  POSTCONDITION(list_is_valid(__write_set, src));
  POSTCONDITION(list_is_valid(__write_set, dst));
  RECORD_DEAD(dst);
  RECORD_DEAD(src);
}

//////////////// POINTER PREDICATES IMPLEMENTATION ////////////////

/////////////////////////////////////
// Instrumentation of the __reach_any_next predicate
/////////////////////////////////////

/// @brief Represents an assumption stated using the __maybe_reach_next
/// predicate.
typedef struct {
  bool assumed;
  node_t *through;
  node_t *from;
  node_t *tail;
} __maybe_reach_next_t;

/// Global map used to track pointer assumptions.
/// The assumption at `__maybe_reach_next_map[__CPROVER_POINTER_OBJECT(node)]`
/// is set iff `node` is a pointer to an opaque list object and
/// `__maybe_reach_next(node, prev, tail)` was assumed for this node
/// for some next and head nodes.
__maybe_reach_next_t *__maybe_reach_next_map;

/// @brief Initialises the ghost map to false
void __maybe_reach_next_map_init() {
  __maybe_reach_next_map =
      malloc(__CPROVER_max_symex_objects() * sizeof(__maybe_reach_next_t));
  __CPROVER_array_set(
      __maybe_reach_next_map,
      (__maybe_reach_next_t){
          .assumed = false, .through = NULL, .from = NULL, .tail = NULL});
}

/// @brief Stores an assumption in the global map.
bool __assume_may_reach_next(node_t *through, node_t *from, node_t *tail) {
  if (nondet_bool())
    return false;
  assert(__CPROVER_r_ok(through, 0));
  assert(__CPROVER_r_ok(from, 0));
  assert(__CPROVER_r_ok(tail, 0));
  __maybe_reach_next_map[__CPROVER_POINTER_OBJECT(through)] =
      (__maybe_reach_next_t){
          .assumed = true, .through = through, .from = from, .tail = tail};
  return true;
}

/// @return true iff an assumption __maybe_reach_next(node, prev, tail) exists
/// in the global map.
bool __maybe_reach_next_assumed(node_t *through, node_t *from, node_t *tail) {
  assert(__CPROVER_r_ok(through, 0));
  assert(__CPROVER_r_ok(from, 0));
  assert(__CPROVER_r_ok(tail, 0));
  __maybe_reach_next_t assumption =
      __maybe_reach_next_map[__CPROVER_POINTER_OBJECT(through)];
  return assumption.assumed && (assumption.through == through) &&
         (assumption.from == from) && (assumption.tail == tail);
}

/// @return True iff `through` is a fresh node for which:
/// - `through->prev` is NULL, `from`, or some bogus fresh node
/// - `through->prev` is NULL, `tail`, or a node that satsifies maybe_reach_next
bool __maybe_reach_next(node_t **through, node_t *from, node_t *tail,
                        __CPROVER_context_t *ctx,
                        __CPROVER_contracts_write_set_ptr_t __write_set,
                        size_t lh) {
  // fail if we went too far
  if (lh == 0) {
    __CPROVER_assert(false, "lh bound must be strictly greater than zero");
    return false;
  }

  // lh depth reached in assumption context, allocate an opaque pointer
  // and store assumption
  if (ctx->assume && lh == 1) {
    *through = malloc(0);
    __CPROVER_assume(*through);
    return __assume_may_reach_next(*through, from, tail);
  }

  // opaque pointer reached in an assertion context
  if (!ctx->assume && (*through != NULL) &&
      __maybe_reach_next_assumed(*through, from, tail)) {
    return true;
  }

  // clang-format off
  return (
    __is_fresh(through, sizeof(node_t), ctx)
    &&
    (
      (
         // `prev` is  NULL or is the `from` node or is some bogus object
            __pointer_equals(&(*through)->prev, NULL, ctx)
         || __pointer_equals(&(*through)->prev, from, ctx)
         || __is_fresh(&(*through)->prev, 0, ctx)
      )
      &&
      (
        // next is NULL or the `tail` node or a some other node that can reach tail
           __pointer_equals(&(*through)->next, NULL, ctx)
        || __pointer_equals(&(*through)->next, tail, ctx)
        || __maybe_reach_next(&(*through)->next, (*through), tail, ctx, __write_set, lh-1)
      )
    )
  );
  // clang-format on
}

/// @brief True iff the list is maybe well formed when traversed from the head
/// node: The next node of head is either NULL or the tail node or a node that
/// satisfies __maybe_reach_next.
/// This predicate has correct lists as a subset, but most importantly defines
/// the space of incorrect lists we consider in the analysis. In particular,
/// cyclic lists are not considered, and invalid pointers are not considered
/// (since a function has no way to detect invalid pointers).
bool __maybe_list(list_t **list, __CPROVER_context_t *ctx,
                  __CPROVER_contracts_write_set_ptr_t __write_set, size_t lh) {
  // clang-format off
  return
  (
    (
      __is_fresh(list, sizeof(list_t), ctx) &&
      __pointer_equals(&((*list)->tail.next), NULL, ctx) &&
      __pointer_equals(&((*list)->head.prev), NULL, ctx)
    )
    &&
    (
      (
        // its next node is NULL
        __pointer_equals(&((*list)->head.next), NULL, ctx)
      )
      ||
      (
        // next node is tail and back linking is correct
        __pointer_equals(&((*list)->head.next), &((*list)->tail), ctx)
        &&__pointer_equals(&((*list)->tail.prev), &((*list)->head), ctx)
      )
      ||
      (
        // next node may reach the tail
        __maybe_reach_next(
          &((*list)->head.next), &((*list)->head), &((*list)->tail),
          ctx, __write_set, lh)
      )
    )
  );
  // clang-format on
}

/////////////////////////////////////
// instrumentation of the __can_reach_prev predicate
/////////////////////////////////////

/// @brief Represents an assumption stated using the __can_reach_prev predicate.
typedef struct {
  bool assumed;
  node_t *through;
  node_t *from;
  node_t *head;
} __can_reach_prev_t;

/// Global map used to track pointer assumptions.
/// The assumption at `__can_reach_prev_map[__CPROVER_POINTER_OBJECT(node)]`
/// is set iff `node` is a pointer to an opaque list object and
/// `__can_reach_prev(node, next, head)` was assumed for this node
/// for some next and head nodes.
__can_reach_prev_t *__can_reach_prev_map;

/// @brief Initialises the ghost map to false
void __can_reach_prev_map_init() {
  __can_reach_prev_map =
      malloc(__CPROVER_max_symex_objects() * sizeof(__can_reach_prev_t));
  // default value for assumptions
  __CPROVER_array_set(
      __can_reach_prev_map,
      (__can_reach_prev_t){
          .assumed = false, .through = NULL, .from = NULL, .head = NULL});
}

/// @brief Stores an assumption in the global map
bool __assume_can_reach_prev(node_t *through, node_t *from, node_t *head) {
  if (nondet_bool())
    return false;
  assert(__CPROVER_r_ok(through, 0));
  assert(__CPROVER_r_ok(from, 0));
  assert(__CPROVER_r_ok(head, 0));
  __can_reach_prev_map[__CPROVER_POINTER_OBJECT(through)] =
      (__can_reach_prev_t){
          .assumed = true, .through = through, .from = from, .head = head};
  return true;
}

/// @return true if an assumption `__can_reach_prev(node, next, head)` exists
bool __can_reach_prev_assumed(node_t *through, node_t *from, node_t *head) {
  assert(__CPROVER_r_ok(through, 0));
  assert(__CPROVER_r_ok(from, 0));
  assert(__CPROVER_r_ok(head, 0));
  __can_reach_prev_t assumption =
      __can_reach_prev_map[__CPROVER_POINTER_OBJECT(through)];
  return assumption.assumed && (assumption.through == through) &&
         (assumption.from == from) && (assumption.head == head);
}

/// Instumentation of the `can_reach_prev(node, next, head)` predicate
bool __can_reach_prev(node_t **through, node_t *from, node_t *head,
                      __CPROVER_context_t *ctx,
                      __CPROVER_contracts_write_set_ptr_t __write_set,
                      size_t lh) {
  // fail if we went too far
  if (lh == 0) {
    __CPROVER_assert(false, "lh bound must be strictly greater than zero");
    return false;
  }

  // lh depth reached in assumption context, allocate an opaque pointer
  // and store assumption
  if (ctx->assume && lh == 1) {
    *through = malloc(0);
    __CPROVER_assume(*through);
    return __assume_can_reach_prev(*through, from, head);
  }

  // opaque pointer reached in an assertion context
  if (!ctx->assume && (*through != NULL) &&
      __can_reach_prev_assumed(*through, from, head)) {
    return true;
  }

  //// INITIAL DEFINITION
  // in assumption or assertion contexts, when the lh depth is not
  // reached and the pointer is not opaque, just evaluate the definition
  return __is_fresh(through, sizeof(node_t), ctx) &&
         __pointer_equals(&((*through)->next), from, ctx) &&
         __pointer_equals(&(from->prev), (*through), ctx) &&
         (__pointer_equals(&((*through)->prev), head, ctx) &&
              __pointer_equals(&(head->next), (*through), ctx) ||
          __can_reach_prev(&((*through)->prev), (*through), head, ctx,
                           __write_set, lh - 1));
}

/////////////////////////////////////
// instrumentation of the __can_reach_next predicate (generated)
/////////////////////////////////////

/// @brief Represents an assumption stated using the __can_reach_next predicate.
typedef struct {
  bool assumed;
  node_t *through;
  node_t *from;
  node_t *tail;
} __can_reach_next_t;

/// Global map used to track pointer assumptions.
/// The assumption at `__can_reach_next_map[__CPROVER_POINTER_OBJECT(node)]`
/// is set iff `node` is a pointer to an opaque list object and
/// `__can_reach_next(node, prev, tail)` was assumed for this node
/// for some next and head nodes.
__can_reach_next_t *__can_reach_next_map;

/// @brief Initialises the ghost map to false
void __can_reach_next_map_init() {
  __can_reach_next_map =
      malloc(__CPROVER_max_symex_objects() * sizeof(__can_reach_next_t));
  __CPROVER_array_set(
      __can_reach_next_map,
      (__can_reach_next_t){
          .assumed = false, .through = NULL, .from = NULL, .tail = NULL});
}

/// Makes node point to an opaque object and stores an assumption in the
/// global map.
bool __assume_can_reach_next(node_t *through, node_t *from, node_t *tail) {
  if (nondet_bool())
    return false;
  assert(__CPROVER_r_ok(through, 0));
  assert(__CPROVER_r_ok(from, 0));
  assert(__CPROVER_r_ok(tail, 0));
  __can_reach_next_map[__CPROVER_POINTER_OBJECT(through)] =
      (__can_reach_next_t){
          .assumed = true, .through = through, .from = from, .tail = tail};
  return true;
}

/// Returns true iff an assumption __can_reach_next(node, prev, tail) exists
/// in the global map.
bool __can_reach_next_assumed(node_t *through, node_t *from, node_t *tail) {
  assert(__CPROVER_r_ok(through, 0));
  assert(__CPROVER_r_ok(from, 0));
  assert(__CPROVER_r_ok(tail, 0));
  __can_reach_next_t assumption =
      __can_reach_next_map[__CPROVER_POINTER_OBJECT(through)];
  return assumption.assumed && (assumption.through == through) &&
         (assumption.from == from) && (assumption.tail == tail);
}

/// Instumentation of the `can_reach_prev(node, next, head)` predicate
bool __can_reach_next(node_t **through, node_t *from, node_t *tail,
                      __CPROVER_context_t *ctx,
                      __CPROVER_contracts_write_set_ptr_t __write_set,
                      size_t lh) {

  // fail if we went too far
  if (lh == 0) {
    __CPROVER_assert(false, "lh bound must be strictly greater than zero");
    return false;
  }

  // lh depth reached in assumption context, allocate an opaque pointer
  // and store assumption
  if (ctx->assume && lh == 1) {
    *through = malloc(0);
    __CPROVER_assume(*through);
    return __assume_can_reach_next(*through, from, tail);
  }

  // opaque pointer reached in an assertion context
  if (!ctx->assume && (*through != NULL) &&
      __can_reach_next_assumed(*through, from, tail)) {
    return true;
  }

  // in assumption or assertion contexts, when the lh depth is not
  // reached and the pointer is not opaque, just evaluate the definition
  return __is_fresh(through, sizeof(node_t), ctx) &&
         __pointer_equals(&((*through)->prev), from, ctx) &&
         __pointer_equals(&(from->next), (*through), ctx) &&
         (__pointer_equals(&((*through)->next), tail, ctx) &&
              __pointer_equals(&(tail->prev), (*through), ctx) ||
          __can_reach_next(&((*through)->next), (*through), tail, ctx,
                           __write_set, lh - 1));
}

/// @brief  Instrumented version of the is_in_list predicate
/// @param list pointer to the list object
/// @param node a pointer to a node
/// @param ctx evaluation context
/// @param ws write set
/// @param lh lookahead depth into the structure
/// @return true iff the list object is fresh and
/// (list->head.prev == &list.tail) and (list->tail.next == &list.head)
/// we can reach `list->tail` from `node` directly or through some intermediate
/// object we can reach `list->head` from `node` directly or through some
/// intermediate object
bool __is_in_list(list_t **list, node_t **node, __CPROVER_context_t *ctx,
                  __CPROVER_contracts_write_set_ptr_t __write_set, size_t lh) {
  // clang-format off
  return
  (
    (
      __is_fresh(list, sizeof(list_t), ctx) &&
      __pointer_equals(&((*list)->tail.next), NULL, ctx) &&
      __pointer_equals(&((*list)->head.prev), NULL, ctx)
    )
    &&
    (
      (
        // list is empty and node points to tail
        __pointer_equals(&((*list)->head.next), &((*list)->tail), ctx) &&
        __pointer_equals(&((*list)->tail.prev), &((*list)->head), ctx) &&
        __pointer_equals(node, &((*list)->tail), ctx)
      )
      ||
      (
        // the node is fresh and
        __is_fresh(node, sizeof(node_t), ctx) &&
        (
          (
            // its predecessor is the head node
            __pointer_equals(&((*node)->prev), &((*list)->head), ctx) &&
            __pointer_equals(&((*list)->head.next), (*node), ctx)
          )
          // or some other node that can reach the head
          || __can_reach_prev(&((*node)->prev), (*node), &((*list)->head),
          ctx, __write_set, lh)
        )
        &&
        (
          (
            // its successor is the tail node
            __pointer_equals(&((*node)->next), &((*list)->tail), ctx) &&
            __pointer_equals(&((*list)->tail.prev), (*node), ctx)
          )
          // or some other fresh node that can reach the tail
          || __can_reach_next(&((*node)->next), (*node), &((*list)->tail),
          ctx, __write_set, lh)
        )
      )
    )
  );
  // clang-format on
}

node_t *nondet_node_ptr();

/// @brief  Implementation of __CPROVER_assignable_node_ptr
/// @param ptr target int pointer
/// @param ctx context tracking instance
/// @param ws write set
/// @return true iff the target pointer is assignable
bool __assignable_node_ptr(__CPROVER_contracts_write_set_ptr_t __write_set,
                           node_t **node, __CPROVER_context_t *ctx) {
  // no effect if write set is null
  if (!__write_set)
    return true;

  if (ctx->assume) {
    // in assumption mode, add this location to write set
    __CPROVER_contracts_write_set_append_assignable(__write_set, node,
                                                    sizeof(node_t *));
    return true;
  } else {
    // in assertion mode, check if this location is in the write set
    bool result = __CPROVER_contracts_write_set_check_assignment(
        __write_set, node, sizeof(node_t *));
    // prove inclusion
    __CPROVER_assert(result, "write set inclusion check");
    // havoc the location
    *node = nondet_node_ptr();
    return result;
  }
}

node_t nondet_node();

/// @brief Implementation of __CPROVER_assignable_node_ptr
/// @param ptr target int pointer
/// @param ctx context tracking instance
/// @param ws write set to add to/check against
/// @return true iff the target pointer is assignable
bool __assignable_node(__CPROVER_contracts_write_set_ptr_t __write_set,
                       node_t *node, __CPROVER_context_t *ctx) {
  // no effect if write set is null
  if (!__write_set)
    return true;

  if (ctx->assume) {
    // in assumption mode, add this location to write set
    __CPROVER_contracts_write_set_append_assignable(__write_set, node,
                                                    sizeof(node_t));
    return true;
  } else {
    // in assertion mode, check if this location is in the write set
    bool result = __CPROVER_contracts_write_set_check_assignment(
        __write_set, node, sizeof(node_t));
    // prove inclusion
    __CPROVER_assert(result, "write set inclusion check");
    // havoc the location
    *node = nondet_node();
    return result;
  }
}

///////////// VERIFICATION WRAPPERS & HARNESSES ////////////////////////////////
// proof harness for list_insert_before
// cbmc --bounds-check --pointer-check --pointer-overflow-check
// --external-sat-solver kissat dll_unbounded_dfcc.c
void list_insert_before_harness() {
  __can_reach_prev_map_init();
  __can_reach_next_map_init();
  list_t *list;
  node_t *before;
  node_t *to_add;

  // call the verification wrapper
  list_insert_before(NULL /* default value for the write set */, list, before,
                     to_add);
}

void null_or_seen_harness() {
  __CPROVER_context_t *ctx = __CPROVER_context_new(true);
  bool *fresh1;
  int *fresh2;
  int *seen;
  __CPROVER_assume(__is_fresh(&fresh1, sizeof(*fresh1), ctx));
  __CPROVER_assume(__is_fresh(&fresh2, sizeof(*fresh2), ctx));
  __CPROVER_assume(__null_or_seen(&seen, ctx));
  void *dummy_ptr = seen;

  assert(seen == fresh1 || seen == fresh2 || seen == NULL);
}

void maybe_list_harness() {
  __maybe_reach_next_map_init();
  __can_reach_next_map_init();
  __can_reach_prev_map_init();

  list_t *list;
  size_t lh = 2;
  {
    __CPROVER_context_t *ctx = __CPROVER_context_new(true);
    __CPROVER_assume(__maybe_list(&list, ctx, NULL, lh));
  }
  {
    __CPROVER_context_t *ctx = __CPROVER_context_new(false);
    assert(__maybe_list(&list, ctx, NULL, lh));
  }
}

void list_is_valid_harness() {
  __maybe_reach_next_map_init();
  __can_reach_next_map_init();
  __can_reach_prev_map_init();
  list_t *list;
  list_is_valid(NULL, list);
}
