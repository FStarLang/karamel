open Ctypes
open PosixTypes
open Foreign

open Lowlevel_bindings

let square (x: Unsigned.UInt32.t): Unsigned.UInt32.t =
  square_ x

let point_sum (p1: t_Lowlevel_point structure)
  (p2: t_Lowlevel_point structure) =
  point_sum_ p1 p2

let move_circle (c: t_Lowlevel_circle structure)
  (p: t_Lowlevel_point structure) =
  move_circle_ c p

let my_not (b: t_Lowlevel_my_bool ptr): unit = my_not_ b

let replicate (n: Unsigned.UInt32.t): t_Lowlevel_tr structure= replicate_ n

let maybe_double (n: t_Lowlevel_int_opt structure ptr): unit = maybe_double_ n


let point_to_tuple (p: t_Lowlevel_point structure) =
  (Unsigned.UInt32.to_int (getf p point_x), Unsigned.UInt32.to_int (getf p point_y))

let print_point (p: t_Lowlevel_point structure) =
  Printf.printf "(%d, %d)\n"
    (Unsigned.UInt32.to_int (getf p point_x))
    (Unsigned.UInt32.to_int (getf p point_y))

let print_circle (c: t_Lowlevel_circle structure) =
  Printf.printf "%d " (Unsigned.UInt32.to_int (getf c circle_r));
  print_point (getf c circle_c)


let _ =
  assert (Unsigned.UInt32.to_int (square (Unsigned.UInt32.of_int 5)) = 25)

let _ =
  let p1 = make t_Lowlevel_point in
  let _ = setf p1 point_x (Unsigned.UInt32.of_int 3) in
  let _ = setf p1 point_y (Unsigned.UInt32.of_int 5) in

  let p2 = make t_Lowlevel_point in
  let _ = setf p2 point_x (Unsigned.UInt32.of_int 3) in
  let _ = setf p2 point_y (Unsigned.UInt32.of_int 5) in

  let p_ret = point_sum p1 p2 in
  assert (point_to_tuple p_ret = (6, 10))

let _ =
  let centre = make t_Lowlevel_point in
  let _ = setf centre point_x (Unsigned.UInt32.of_int 3) in
  let _ = setf centre point_y (Unsigned.UInt32.of_int 5) in

  let circle = make t_Lowlevel_circle in
  let _ = setf circle circle_c centre in
  let _ = setf circle circle_r (Unsigned.UInt32.of_int 5) in

  let p = make t_Lowlevel_point in
  let _ = setf p point_x (Unsigned.UInt32.of_int 3) in
  let _ = setf p point_y (Unsigned.UInt32.of_int 2) in

  let circle_ret = move_circle circle p in
  let centre_ret = getf circle_ret circle_c in
  assert (point_to_tuple centre_ret = (6, 7));
  assert (Unsigned.UInt32.to_int (getf circle_ret circle_r) = 5)

let _ =
  let b_ptr = allocate t_Lowlevel_my_bool t_Lowlevel_MyTrue in
  let _ = my_not b_ptr in
  let v = !@ b_ptr in
  assert (v = t_Lowlevel_MyFalse)

let _ =
  let arg = Unsigned.UInt32.of_int 6 in
  let d = replicate arg in
  let f = getf d tr__0 in
  assert (getf f t_K___uint32_t_uint32_t_uint32_t_uint32_t_uint32_t_fst = arg);
  assert (getf f t_K___uint32_t_uint32_t_uint32_t_uint32_t_uint32_t_snd = arg);
  assert (getf f t_K___uint32_t_uint32_t_uint32_t_uint32_t_uint32_t_thd = arg);
  assert (getf f t_K___uint32_t_uint32_t_uint32_t_uint32_t_uint32_t_f3 = arg);
  assert (getf f t_K___uint32_t_uint32_t_uint32_t_uint32_t_uint32_t_f4 = arg)

let _ =
  let n = make t_Lowlevel_int_opt in
  setf n int_opt_tag t_Lowlevel_IntSome;
  setf n int_opt__0 (Unsigned.UInt32.of_int 12);
  let n_ptr = allocate t_Lowlevel_int_opt n in
  maybe_double n_ptr;
  let v = !@ n_ptr in
  assert (getf v int_opt_tag = t_Lowlevel_IntSome && getf v int_opt__0 = Unsigned.UInt32.of_int 24)
