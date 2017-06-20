module Abbrev

open FStar
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
open TestLib

type lbytes l1 l2 =
  b:buffer Int32.t{length b = l1 + l2}

type lbytes' l =
  lbytes l 1

// The test is just about making sure that this compiles properly
type bytes4 = lbytes 4 8

val main: Int32.t -> Buffer.buffer (Buffer.buffer C.char) ->
  Stack Int32.t (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  push_frame ();
  let b: lbytes' 1 = Buffer.create 0l 2ul in
  pop_frame ();
  C.exit_success
