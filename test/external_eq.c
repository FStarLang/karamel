#include "ExternalEq.h"

K___ExternalEq_t_ExternalEq_t mk_pair_t() {
  return (K___ExternalEq_t_ExternalEq_t){ .fst = 0, .snd = 1 };
}

bool __eq__ExternalEq_t(t x, t y) {
  return x == y;
}
