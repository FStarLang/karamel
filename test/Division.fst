module Division

open FStar.HyperStack.ST

(* This test checks that the runtime behavior of division and modulo
   coincide with what we can prove in F*, in particular as signs of the
   dividend and divisor vary. C's semantics for division and remainder
   (and hence the one in the signed F* integers) truncate the division
   towards zero. The remainder must satisfy the identity 'a * (a/b) +
   a%b = a', so it has the sign of the dividend if nonzero. *)

let test_i8
  (x y : Int8.t{Int8.v y =!= 0 /\ Int8.fits (Int8.v x / Int8.v y)})
  (rdiv : Int8.t {rdiv == x `Int8.div` y})
  (rrem : Int8.t {rrem == x `Int8.rem` y})
  : Stack unit (requires fun _ -> True) (ensures fun _ _ _ -> True) =
  let open FStar.Int8 in
  if x `div` y <> rdiv || x `rem` y <> rrem then
    LowStar.Failure.failwith "failed"

let test_i16
  (x y : Int16.t{Int16.v y =!= 0 /\ Int16.fits (Int16.v x / Int16.v y)})
  (rdiv : Int16.t {rdiv == x `Int16.div` y})
  (rrem : Int16.t {rrem == x `Int16.rem` y})
  : Stack unit (requires fun _ -> True) (ensures fun _ _ _ -> True) =
  let open FStar.Int16 in
  if x `div` y <> rdiv || x `rem` y <> rrem then
    LowStar.Failure.failwith "failed"

let test_i32
  (x y : Int32.t{Int32.v y =!= 0 /\ Int32.fits (Int32.v x / Int32.v y)})
  (rdiv : Int32.t {rdiv == x `Int32.div` y})
  (rrem : Int32.t {rrem == x `Int32.rem` y})
  : Stack unit (requires fun _ -> True) (ensures fun _ _ _ -> True) =
  let open FStar.Int32 in
  if x `div` y <> rdiv || x `rem` y <> rrem then
    LowStar.Failure.failwith "failed"

let test_i64
  (x y : Int64.t{Int64.v y =!= 0 /\ Int64.fits (Int64.v x / Int64.v y)})
  (rdiv : Int64.t {rdiv == x `Int64.div` y})
  (rrem : Int64.t {rrem == x `Int64.rem` y})
  : Stack unit (requires fun _ -> True) (ensures fun _ _ _ -> True) =
  let open FStar.Int64 in
  if x `div` y <> rdiv || x `rem` y <> rrem then
    LowStar.Failure.failwith "failed"

let main () =
  test_i8 7y    2y    3y    1y;
  test_i8 7y    (-2y) (-3y) 1y;
  test_i8 (-7y) 2y    (-3y) (-1y);
  test_i8 (-7y) (-2y) 3y    (-1y);

  test_i16 7s    2s    3s    1s;
  test_i16 7s    (-2s) (-3s) 1s;
  test_i16 (-7s) 2s    (-3s) (-1s);
  test_i16 (-7s) (-2s) 3s    (-1s);

  test_i32 7l    2l    3l    1l;
  test_i32 7l    (-2l) (-3l) 1l;
  test_i32 (-7l) 2l    (-3l) (-1l);
  test_i32 (-7l) (-2l) 3l    (-1l);

  test_i64 7L    2L    3L    1L;
  test_i64 7L    (-2L) (-3L) 1L;
  test_i64 (-7L) 2L    (-3L) (-1L);
  test_i64 (-7L) (-2L) 3L    (-1L);
  0l
