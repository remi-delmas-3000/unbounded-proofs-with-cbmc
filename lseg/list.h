#ifndef LIST_H_INCLUDED
#define LIST_H_INCLUDED
#include <stdlib.h>

typedef struct list_s {
  int value;
  struct list_s *next;
} list_t;

#endif
