module Scope

//
open FStar.Int32
open FStar.HyperStack.ST
open TestLib

let foo (): Stack bool (fun _ -> true) (fun _ _ _ -> true) =
  true

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  Stack Int32.t (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  push_frame ();
  let bof = Buffer.create 0l 1ul in
  let bbof = Buffer.create bof 1ul in
  if foo () then begin
    let bof' = Buffer.create 2l 1ul in
    Buffer.upd bbof 0ul bof'
  end;
  let bof'' = Buffer.create 1l 1ul in
  let tmp = Buffer.index bbof 0ul in
  check (Buffer.index tmp 0ul) 2l;
  check (Buffer.index bof 0ul) 0l;
  check (Buffer.index bof'' 0ul) 1l;
  pop_frame ();
  C.exit_success

