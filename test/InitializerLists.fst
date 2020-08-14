module InitializerLists

open FStar.HyperStack.ST

module B = LowStar.Buffer

let x1 = LowStar.Buffer.gcmalloc_of_list FStar.HyperStack.root ([ ] <: list UInt32.t)
let x2 = LowStar.Buffer.gcmalloc_of_list FStar.HyperStack.root ([ 0ul ] <: list UInt32.t)
let x3 = LowStar.Buffer.gcmalloc_of_list FStar.HyperStack.root ([ 0ul; 0ul ] <: list UInt32.t)

let f (x: UInt32.t): St unit = ()

[@@ CPrologue "\
#define Test_f(X) \
  _Static_assert (sizeof Test_x1 == 0, \"\"); \
  _Static_assert (sizeof Test_x2 == 4, \"\"); \
  _Static_assert (sizeof Test_x3 == 8, \"\"); \
  _Static_assert (sizeof y2 == 4, \"\"); \
  _Static_assert (sizeof y3 == 8, \"\"); \
\
"]
private
let x = 0l

let main (): St Int32.t =
  push_frame ();
  let y2 = B.alloca_of_list [ 0ul ] in
  let y3 = B.alloca_of_list [ 0ul; 0ul ] in
  f 0ul;
  pop_frame ();
  x

