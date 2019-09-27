open Ctypes
open PosixTypes
open Foreign

module Lowlevel = Lowlevel_bindings.Bindings(Lowlevel_stubs)
module A2 = A2_bindings.Bindings(A2_stubs)

let point_sum (p1: Lowlevel.b_point)
  (p2: Lowlevel.b_point) =
  Lowlevel.point_sum p1 p2

let point_sum2 (p1: A2.b_point)
  (p2: A2.b_point) =
  A2.a2_point_sum2 p1 p2

let move_circle (c: Lowlevel.d_circle)
  (p: Lowlevel.b_point) =
  Lowlevel.move_circle c p

let point_to_tuple (p: Lowlevel.b_point) =
  (Unsigned.UInt32.to_int (getf p Lowlevel.b_point_x), Unsigned.UInt32.to_int (getf p Lowlevel.b_point_y))

let _ =
  let open Lowlevel in
  assert ((!@ c) = Unsigned.UInt32.of_int 6);
  assert (getf (!@ p) b_point_x = Unsigned.UInt32.of_int 8);
  assert (getf (!@ p) b_point_y = Unsigned.UInt32.of_int 13);

  let centre = make b_point in
  let _ = setf centre b_point_x (Unsigned.UInt32.of_int 3) in
  let _ = setf centre b_point_y (Unsigned.UInt32.of_int 5) in
  
  let circle = make d_circle in
  let _ = setf circle d_circle_c centre in
  let _ = setf circle d_circle_r (Unsigned.UInt32.of_int 5) in
  
  let p = make b_point in
  let _ = setf p b_point_x (Unsigned.UInt32.of_int 3) in
  let _ = setf p b_point_y (Unsigned.UInt32.of_int 2) in
  
  let circle_ret = move_circle circle p in
  let centre_ret = getf circle_ret d_circle_c in
  assert (point_to_tuple centre_ret = (6, 7));
  assert (Unsigned.UInt32.to_int (getf circle_ret d_circle_r) = 5);

  let string_of_backend_type = function
    | Sys.Native -> "Native"
    | Sys.Bytecode -> "Bytecode"
    | Sys.Other s -> s
  in
  Printf.printf "======= End CTypes test (%s)\t======\n" (string_of_backend_type Sys.backend_type)
