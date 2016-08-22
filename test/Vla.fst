module Vla

//
open FStar.HST
open TestLib

module U32 = FStar.UInt32

let test (_: unit): Stl unit =
  push_frame ();
  // Generates a zero-filled buffer.
  let b1 = Buffer.create 0ul 256ul in
  // Generates a call to memset (non-constant size, until we implement constant folding)
  let b2 = Buffer.create 0ul (U32 (128ul +^ 128ul)) in
  // Generates a for-loop (non-zero initializer)
  let b3 = Buffer.create 16ul 256ul in
  pop_frame ()

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) -> Stl C.int
let main argc argv =
  test ();
  C.exit_success

