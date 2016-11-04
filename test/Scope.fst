module Scope

//
open FStar.Int32
open FStar.ST
open TestLib

let foo (): ST.Stack bool (fun _ -> true) (fun _ _ _ -> true) =
  true

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  Stack Int32.t (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  push_frame ();
  let buf = Buffer.create 0l 1ul in
  let bbuf = Buffer.create buf 1ul in
  if foo () then begin
    let buf' = Buffer.create 2l 1ul in
    Buffer.upd bbuf 0ul buf'
  end;
  let buf'' = Buffer.create 1l 1ul in
  let tmp = Buffer.index bbuf 0ul in
  check (Buffer.index tmp 0ul) 2l;
  check (Buffer.index buf 0ul) 0l;
  check (Buffer.index buf'' 0ul) 1l;
  pop_frame ();
  C.exit_success

