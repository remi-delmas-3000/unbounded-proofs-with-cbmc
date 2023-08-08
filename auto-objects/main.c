#include <assert.h>
#include <stdlib.h>

// does not seem to do anything.
typedef struct list_s {
    int value;
    struct list_s *next;
} list_t;

int main() {
    list_t *list;
    if(list) {
        int value = list->value;
    }
}

