module AllocFree

open FStar.HyperStack
open FStar.HyperStack.ST

let test1 () : Stack unit (fun _ -> False) (fun _ _ _ -> True) =
  let b = FStar.Buffer.rcreate_mm root 1uL 999ul in
  FStar.Buffer.rfree b

let test2 () : Stack unit (fun _ -> False) (fun _ _ _ -> True) =
  [@@CInline] let b = FStar.Buffer.rcreate_mm root 1uL 999ul in
  FStar.Buffer.rfree b

let main () = 0l
