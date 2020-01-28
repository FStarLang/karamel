open Ctypes
open PosixTypes
open Foreign

module Lowlevel = Lowlevel_bindings.Bindings(Lowlevel_stubs)
module Ctypes1 = Ctypes1_bindings.Bindings(Ctypes1_stubs)
open Ctypes1
module Ctypes2 = Ctypes2_bindings.Bindings(Ctypes2_stubs)

let point_sum (p1: ctypes1_point)
  (p2: ctypes1_point) =
  Lowlevel.point_sum p1 p2

let point_sum2 (p1: Ctypes1.ctypes1_point)
  (p2: Ctypes1.ctypes1_point) =
  Ctypes2.ctypes2_point_sum2 p1 p2

let move_circle (c: Lowlevel.ctypes3_circle)
  (p: ctypes1_point) =
  Lowlevel.move_circle c p

let point_to_tuple (p: ctypes1_point) =
  (Unsigned.UInt32.to_int (getf p ctypes1_point_x), Unsigned.UInt32.to_int (getf p ctypes1_point_y))

let _ =
  let open Lowlevel in
  assert ((!@ c) = Unsigned.UInt32.of_int 6);
  assert (getf (!@ p) ctypes1_point_x = Unsigned.UInt32.of_int 8);
  assert (getf (!@ p) ctypes1_point_y = Unsigned.UInt32.of_int 13);

  let centre = make ctypes1_point in
  let _ = setf centre ctypes1_point_x (Unsigned.UInt32.of_int 3) in
  let _ = setf centre ctypes1_point_y (Unsigned.UInt32.of_int 5) in
  
  let circle = make ctypes3_circle in
  let _ = setf circle ctypes3_circle_c centre in
  let _ = setf circle ctypes3_circle_r (Unsigned.UInt32.of_int 5) in
  
  let p = make ctypes1_point in
  let _ = setf p ctypes1_point_x (Unsigned.UInt32.of_int 3) in
  let _ = setf p ctypes1_point_y (Unsigned.UInt32.of_int 2) in
  
  let circle_ret = move_circle circle p in
  let centre_ret = getf circle_ret ctypes3_circle_c in
  assert (point_to_tuple centre_ret = (6, 7));
  assert (Unsigned.UInt32.to_int (getf circle_ret ctypes3_circle_r) = 5);

  let b_ptr = allocate my_bool my_bool_MyTrue in
  let _ = my_not b_ptr in
  let v = !@ b_ptr in
  assert (v = my_bool_MyFalse);

  let b2_ptr = allocate my_bool my_bool_MyFalse in
  let _ = my_not_pointer b2_ptr in
  let v = !@ b2_ptr in
  assert (v = my_bool_MyTrue);
  
  let arg = Unsigned.UInt32.of_int 6 in
  let f = replicate arg in
  assert (getf f t___uint32_t_uint32_t_uint32_t_uint32_t_uint32_t_fst = arg);
  assert (getf f t___uint32_t_uint32_t_uint32_t_uint32_t_uint32_t_snd = arg);
  assert (getf f t___uint32_t_uint32_t_uint32_t_uint32_t_uint32_t_thd = arg);
  assert (getf f t___uint32_t_uint32_t_uint32_t_uint32_t_uint32_t_f3 = arg);
  assert (getf f t___uint32_t_uint32_t_uint32_t_uint32_t_uint32_t_f4 = arg);
  
  let n = make int_opt in
  setf n int_opt_tag int_opt_tags_IntSome;
  setf n int_opt__0 (Unsigned.UInt32.of_int 12);
  let n_ptr = allocate int_opt n in
  maybe_double n_ptr;
  let v = !@ n_ptr in
  assert (getf v int_opt_tag = int_opt_tags_IntSome && getf v int_opt__0 = Unsigned.UInt32.of_int 24);
  
  let arg1 = (Unsigned.UInt32.of_int 5) in
  let e1 = make_L arg1 in
  assert (getf e1 eith_tag = eith_tags_L && getf (getf e1 eith_u) eith_val_case_L = arg1);
  
  let arg2 = (Unsigned.UInt16.of_int 7) in
  let e2 = make_R arg2 in
  assert (getf e2 eith_tag = eith_tags_R && getf (getf e2 eith_u) eith_val_case_R = arg2);
  
  let n_ptr = allocate Lowlevel.eith e2 in
  flip_t n_ptr;
  let v = !@ n_ptr in
  assert (getf v eith_tag = eith_tags_L && getf (getf v eith_u) eith_val_case_L = Unsigned.UInt32.of_int 7);

  let string_of_backend_type = function
    | Sys.Native -> "Native"
    | Sys.Bytecode -> "Bytecode"
    | Sys.Other s -> s
  in
  Printf.printf "======= End CTypes test (%s)\t======\n" (string_of_backend_type Sys.backend_type)
