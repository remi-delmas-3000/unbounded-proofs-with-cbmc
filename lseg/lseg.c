#include "lseg.h"

// prove the lseg transitivity lemma
int main() {
  __lseg_map_init();
  list_t *x;
  list_t *y;
  list_t *z;
  lseg_lemma(x, y, z);
  return 0;
}
