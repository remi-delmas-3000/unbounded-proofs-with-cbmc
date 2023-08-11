#include <stdlib.h>
typedef struct node_s {
  struct node_s *next
} node_t;

// pointer-typed fields and vars
// A1.next main::list main::list->next main::1::n main::1::n->next
int main() {
  // PT(A1.next) = {}
  node_t *list = NULL;
  // PT(A1.next) = {}
  // PT(main::list) = {NULL}
  // PT(main::list->next) = {}
  while (nondet()) {
    // (loop fixpoint)
    // --------
    // PT(A1.next)= {NULL, &A1}
    // PT(main::list)= {NULL, &A1}
    // PT(main::list->next)= {&A1}
    node_t *n = malloc(sizeof(node_t)); // abstract dyn object &A1
    // updates:
    // - PT(n) = {&A1}
    // - PT(n->next) = PT(A1.next)
    // --------
    // PT(A1.next) = {NULL, &A1}
    // PT(main::list) = {NULL, &A1}
    // PT(main::list->next) = {&A1}
    // PT(main::1::n) = {&A1}
    // PT(main::1::n->next) = {NULL, &A1}
    n->next = list;
    // updates:
    // - PT(n->next) = PT(list),
    // - for each t in PT(n), PT(t.next) = PT(t.next) union PT(list)
    // --------
    // PT(A1.next) = {NULL, &A1}
    // PT(main::list) = {NULL, &A1}
    // PT(main::list->next) = {&A1}
    // PT(main::1::n) = {&A1}
    // PT(main::1::n->next) = {NULL, &A1}
    list = n;
    // updates PT(list) = PT(n), PT(list->next) = PT(n->next)
    // --------
    // PT(A1.next) = {NULL, &A1}
    // PT(main::list) = {&A1}
    // PT(main::list->next) = {NULL, &A1}
    // PT(main::1::n) = {&A1}
    // PT(main::1::n->next) = {NULL, &A1}
  }
  // (merge)
  // --------
  // PT(A1.next)= {NULL, &A1}
  // PT(main::list)= {NULL, &A1}
  // PT(main::list->next)= {&A1}
}
