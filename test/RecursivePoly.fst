module RecursivePoly

open FStar.HyperStack.ST

module B = FStar.Buffer

type pointer (t: Type0) =
  b:B.buffer t { B.length b = 1 }

#set-options "--__no_positivity"
noeq
type linked_list (a: Type0) =
  | Null
  | Cons: elt:a -> next:pointer (linked_list a) -> linked_list a

let f (x: linked_list FStar.UInt32.t): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  ()

let g (x: linked_list FStar.UInt64.t): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  ()

let main () =
  C.EXIT_SUCCESS
