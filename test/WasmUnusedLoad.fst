module WasmUnusedLoad

module B = LowStar.Buffer
open FStar.HyperStack.ST

(* Keep an ignored load in the Wasm backend. The inlining annotation ensures
   the load reaches the optimizer immediately followed by drop. *)
let read_and_ignore (p: B.buffer UInt64.t): Stack unit
  (fun h -> B.live h p /\ B.length p > 0)
  (fun _ _ _ -> True)
=
  [@@CInline] let x = B.index p 0ul in
  LowStar.Ignore.ignore x

let main (): Stack Int32.t (fun _ -> True) (fun _ _ _ -> True) =
  push_frame ();
  let p = B.alloca 42UL 2ul in
  read_and_ignore p;
  pop_frame ();
  0l
