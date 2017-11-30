#include "CustomEq.h"

bool __eq__CustomEq_point(point p1, point p2) {
  return p1.x == p2.x && p1.y == p2.y;
}
