module VariableMergeAlias

module B = LowStar.Buffer
module HST = FStar.HyperStack.ST

let two (): HST.Stack UInt32.t
  (fun _ -> True) (fun _ _ _ -> True)
= 2ul

(* Do not reuse cell for other: alias must still read 1. *)
let test_alias (): HST.Stack UInt32.t
  (fun _ -> True) (fun _ _ _ -> True)
= HST.push_frame ();
  let cell = B.alloca 0ul 1ul in
  B.upd cell 0ul 1ul;
  let alias = cell in
  let other = two () in
  let result = UInt32.add_mod (B.index alias 0ul) other in
  HST.pop_frame ();
  result

let main (): HST.Stack Int32.t
  (fun _ -> True) (fun _ _ _ -> True)
= if test_alias () = 3ul then 0l else 1l
