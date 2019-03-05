open Ctypes
open PosixTypes
open Foreign

module Lowlevel = Lowlevel_bindings.Bindings(Lowlevel_stubs)

let square (x: Unsigned.UInt32.t): Unsigned.UInt32.t = Lowlevel.square x

let point_sum (p1: Lowlevel.point)
  (p2: Lowlevel.point) =
  Lowlevel.point_sum p1 p2

let move_circle (c: Lowlevel.circle)
  (p: Lowlevel.point) =
  Lowlevel.move_circle c p

let my_not (b: Lowlevel.my_bool ptr): unit = Lowlevel.my_not b

let replicate (n: Unsigned.UInt32.t): Lowlevel.tr = Lowlevel.replicate n

let maybe_double (n: Lowlevel.int_opt ptr): unit = Lowlevel.maybe_double n


(* let make_L (x: Unsigned.UInt32.t): Lowlevel.eith = Lowlevel.make_L x
 * 
 * let make_R (x: Unsigned.UInt16.t): Lowlevel.eith = Lowlevel.make_R x
 * 
 * let flip_t (p: Lowlevel.eith ptr): unit = Lowlevel.flip_t p *)


let point_to_tuple (p: Lowlevel.point) =
  (Unsigned.UInt32.to_int (getf p Lowlevel.point_x), Unsigned.UInt32.to_int (getf p Lowlevel.point_y))


let _ =
  assert (Unsigned.UInt32.to_int (square (Unsigned.UInt32.of_int 5)) = 25)

let _ =
  let open Lowlevel in
  let centre = make point in
  let _ = setf centre point_x (Unsigned.UInt32.of_int 3) in
  let _ = setf centre point_y (Unsigned.UInt32.of_int 5) in

  let circle = make circle in
  let _ = setf circle circle_c centre in
  let _ = setf circle circle_r (Unsigned.UInt32.of_int 5) in

  let p = make point in
  let _ = setf p point_x (Unsigned.UInt32.of_int 3) in
  let _ = setf p point_y (Unsigned.UInt32.of_int 2) in

  let circle_ret = move_circle circle p in
  let centre_ret = getf circle_ret circle_c in
  assert (point_to_tuple centre_ret = (6, 7));
  assert (Unsigned.UInt32.to_int (getf circle_ret circle_r) = 5)

let _ =
  let open Lowlevel in
  let b_ptr = allocate my_bool my_bool_MyTrue in
  let _ = my_not b_ptr in
  let v = !@ b_ptr in
  assert (v = my_bool_MyFalse)

let _ =
  let open Lowlevel in
  let arg = Unsigned.UInt32.of_int 6 in
  let d = replicate arg in
  let f = getf d tr__0 in
  assert (getf f t_K___uint32_t_uint32_t_uint32_t_uint32_t_uint32_t_fst = arg);
  assert (getf f t_K___uint32_t_uint32_t_uint32_t_uint32_t_uint32_t_snd = arg);
  assert (getf f t_K___uint32_t_uint32_t_uint32_t_uint32_t_uint32_t_thd = arg);
  assert (getf f t_K___uint32_t_uint32_t_uint32_t_uint32_t_uint32_t_f3 = arg);
  assert (getf f t_K___uint32_t_uint32_t_uint32_t_uint32_t_uint32_t_f4 = arg)

let _ =
  let open Lowlevel in
  let n = make int_opt in
  setf n int_opt_tag int_opt_tags_IntSome;
  setf n int_opt__0 (Unsigned.UInt32.of_int 12);
  let n_ptr = allocate int_opt n in
  maybe_double n_ptr;
  let v = !@ n_ptr in
  assert (getf v int_opt_tag = int_opt_tags_IntSome && getf v int_opt__0 = Unsigned.UInt32.of_int 24)

