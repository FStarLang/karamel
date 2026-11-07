module HoistScope

open FStar.HyperStack.ST
open FStar.Int32
open LowStar.Printf

(* Test hoisting with local scopes: if/else branches. *)

let test_if_else (): St unit =
  push_frame ();
  let x = 10l in
  let cond = true in
  if cond then begin
    let y = x +^ 5l in
    printf "then: y=%ld\n" y done
  end else begin
    let z = x -^ 5l in
    printf "else: z=%ld\n" z done
  end;
  printf "test_if_else: x=%ld\n" x done;
  pop_frame ()

(* Declarations in both branches with a merge afterward. *)
let test_merge (): St unit =
  push_frame ();
  let a = 1l in
  let b = 2l in
  printf "before: a=%ld b=%ld\n" a b done;
  let c = if a >^ 0l then begin
    let t = a +^ b in
    printf "then: t=%ld\n" t done;
    t
  end else begin
    let t = a -^ b in
    printf "else: t=%ld\n" t done;
    t
  end in
  printf "test_merge: c=%ld\n" c done;
  pop_frame ()

(* Nested scopes. *)
let test_nested_scope (): St unit =
  push_frame ();
  let x = 1l in
  printf "outer: x=%ld\n" x done;
  begin
    let y = x +^ 1l in
    printf "inner: y=%ld\n" y done;
    begin
      let z = y +^ 1l in
      printf "innermost: z=%ld\n" z done
    end
  end;
  let w = x +^ 10l in
  printf "test_nested_scope: w=%ld\n" w done;
  pop_frame ()

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  St C.exit_code
let main argc argv =
  push_frame ();
  test_if_else ();
  test_merge ();
  test_nested_scope ();
  pop_frame ();
  C.EXIT_SUCCESS
