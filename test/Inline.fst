module Inline

open FStar
open FStar.HyperStack
open FStar.HyperStack.ST
open TestLib

module I32 = FStar.Int32

let alloc_and_init (i: Int32.t): StackInline (Buffer.buffer Int32.t)
  (requires (fun h0 -> FStar.Int.size (I32.v i) 16 /\ is_stack_region h0.tip))
    // JP: why do I have to manually write the hypothesis above?
  (ensures (fun h0 b h1 ->
    let open FStar.Buffer in
    length b = 2 /\
    (forall (b0: buffer Int32.t). live h0 b0 ==> live h1 b0) /\
    live h1 b))
=
  let open FStar.Int32 in
  Buffer.createL [i; FStar.Int32.add i 1l]

// JP: couldn't figure out how to define trivial_pre and trivial_post so that I
// don't have to repeat the [fun _ _ _ ...]

val main: Int32.t -> Buffer.buffer (Buffer.buffer C.char) ->
  Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  // JP: found no way to make this work with [with_frame]!
  push_frame ();
  let buf = alloc_and_init 0l in
  let buf' = alloc_and_init 2l in
  // If [alloc_and_init] is compiled as a separate function, then the second
  // call will override the initial value and the check32 will fail.
  check32 (Buffer.index buf 1ul) 1l;
  pop_frame ();
  C.EXIT_SUCCESS
