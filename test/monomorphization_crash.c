#include "monomorphization_crash.h"
#include "MonomorphizationCrash.h"

extern Abstract_t mk_t() {
  return (Abstract_t){ .x = 0 };
}
extern bool __eq__Abstract_t(const Abstract_t *x, const Abstract_t *y) {
  return x->x == y->x;
}

