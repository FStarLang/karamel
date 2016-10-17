module Vla

//
open FStar.ST
open TestLib

module U32 = FStar.UInt32

let test (_: unit): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  push_frame ();
  // Generates a zero-filled buffer.
  let b1 = Buffer.create 0ul 256ul in
  // Generates a call to memset (non-constant size, until we implement constant folding)
  let b2 = Buffer.create 0ul (U32 (128ul +^ 128ul)) in
  // Generates a for-loop (non-zero initializer)
  let b3 = Buffer.create 16ul 256ul in
  // Generates an initializer list
  let b4 = Buffer.createL [ 0x0ul; 0x1ul; 0x2ul; 0x3ul ] in
  pop_frame ()

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  Stack Int32.t (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  push_frame ();
  test ();
  pop_frame ();
  C.exit_success

