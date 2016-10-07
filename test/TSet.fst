module TSet

open FStar.HyperStack
open FStar.HST

val refs: p:ref int -> GTot (TSet.set Heap.aref)
let refs p = TSet.empty #Heap.aref

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  HST.Stack Int32.t (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  push_frame ();
  pop_frame ();
  C.exit_success
