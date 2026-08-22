module HoistArray

open FStar.HyperStack.ST
open FStar.UInt32
open LowStar.Printf
open LowStar.BufferOps

module B = LowStar.Buffer

(* Test hoisting of array local variables. *)

(* Array with constant size at the top -- should keep init. *)
let test_const_array (): St unit =
  push_frame ();
  let buf = B.alloca 0ul 4ul in
  buf.(0ul) <- 10ul;
  buf.(1ul) <- 20ul;
  buf.(2ul) <- 30ul;
  buf.(3ul) <- 40ul;
  let v0 = buf.(0ul) in
  let v1 = buf.(1ul) in
  let v2 = buf.(2ul) in
  let v3 = buf.(3ul) in
  printf "test_const_array: %ul %ul %ul %ul\n" v0 v1 v2 v3 done;
  pop_frame ()

(* Array with constant size after a statement -- decl should be separated. *)
let test_array_after_stmt (): St unit =
  push_frame ();
  let x = 5ul in
  printf "x=%ul\n" x done;
  let buf = B.alloca 0ul 3ul in
  buf.(0ul) <- x;
  buf.(1ul) <- x +^ 1ul;
  buf.(2ul) <- x +^ 2ul;
  let v0 = buf.(0ul) in
  let v1 = buf.(1ul) in
  let v2 = buf.(2ul) in
  printf "test_array_after_stmt: %ul %ul %ul\n" v0 v1 v2 done;
  pop_frame ()

(* Array with initializer list. *)
let test_createL (): St unit =
  push_frame ();
  let buf = B.alloca_of_list [ 100ul; 200ul; 300ul ] in
  let v0 = buf.(0ul) in
  let v1 = buf.(1ul) in
  let v2 = buf.(2ul) in
  printf "test_createL: %ul %ul %ul\n" v0 v1 v2 done;
  pop_frame ()

val main: FStar.Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  St C.exit_code
let main argc argv =
  push_frame ();
  test_const_array ();
  test_array_after_stmt ();
  test_createL ();
  pop_frame ();
  C.EXIT_SUCCESS
