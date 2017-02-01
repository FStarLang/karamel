module Hoisting
open FStar.Int32
open FStar.ST

open TestLib

let test () =
  touch 0l;
  let z = 1l in
  let x =
    let y =
      let b1 = true in
      let b2 = false in
      b1 || b2
    in
    let a = 2l in
    check a 2l;
    let b = 4l in
    if let z = true in z = y then begin
      touch 0l;
      let a = 8l in
      touch 0l;
      check (a +^ b) 12l;
      a +^ b
    end else begin
      touch 0l;
      let b = 16l in
      touch 0l;
      check (a -^ b) (0l -^ 14l);
      a -^ b
    end
  in
  let y = 32l in
  check (x +^ y +^ z) 45l;
  x +^ y

let test' (): St Int32.t =
  let x = true in
  if x = false then
    ()
  else begin
    let x = 1l in
    let y = x +^ 2l in
    check y 3l
  end;
  4l

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  ST.Stack Int32.t (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  push_frame ();
  check (test ()) 44l;
  check (test' ()) 4l;
  pop_frame ();
  C.exit_success
