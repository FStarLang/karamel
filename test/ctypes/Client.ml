open Ctypes
open PosixTypes
open Foreign

open Lowlevel_bindings

let square x =
  square_ x

let point_sum (p1: t_Lowlevel_point structure)
  (p2: t_Lowlevel_point structure) =
  point_sum_ p1 p2

let move_circle (c: t_Lowlevel_circle structure)
  (p: t_Lowlevel_point structure) =
  move_circle_ c p

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
