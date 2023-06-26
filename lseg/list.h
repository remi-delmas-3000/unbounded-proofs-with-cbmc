#ifndef LIST_H_INCLUDED
#define LIST_H_INCLUDED
#include <stdlib.h>

// a linked list
typedef struct list_s {
  int value;
  struct list_s *next;
} list_t;

// requires lseg(x, NULL)
// requires lseg(y, NULL)
// ensures lseg(y, NULL)
// ensures lseg(x, y)
void list_append(list_t *x, list_t *y);

#endif
