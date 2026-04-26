module HoistInt

open FStar.HyperStack.ST
open FStar.Int32
open LowStar.Printf

(* Test hoisting of machine integer local variables. *)

let test_basic (): St unit =
  push_frame ();
  let x = 1l in
  let y = 2l in
  let z = x +^ y in
  printf "test_basic: x=%ld y=%ld z=%ld\n" x y z done;
  pop_frame ()

(* Declarations after a statement should get their init separated. *)
let test_decl_after_stmt (): St unit =
  push_frame ();
  let a = 10l in
  printf "a=%ld\n" a done;
  let b = 20l in
  let c = a +^ b in
  printf "test_decl_after_stmt: b=%ld c=%ld\n" b c done;
  pop_frame ()

(* Nested let-bindings in initializer. *)
let test_nested_init (): St unit =
  push_frame ();
  let x =
    let a = 3l in
    let b = 4l in
    a +^ b
  in
  printf "test_nested_init: x=%ld\n" x done;
  pop_frame ()

(* Multiple int32 variables. *)
let test_many_vars (): St unit =
  push_frame ();
  let a = 1l in
  let b = 2l in
  let c = 3l in
  printf "start: a=%ld b=%ld c=%ld\n" a b c done;
  let d = a +^ b +^ c in
  printf "test_many_vars: d=%ld\n" d done;
  pop_frame ()

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  St C.exit_code
let main argc argv =
  push_frame ();
  test_basic ();
  test_decl_after_stmt ();
  test_nested_init ();
  test_many_vars ();
  pop_frame ();
  C.EXIT_SUCCESS
