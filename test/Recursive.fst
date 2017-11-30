module Recursive

module U32 = FStar.UInt32
module B = FStar.Buffer

type linked_list =
  | Null
  | Cons: elt:U32.t -> next:B.buffer linked_list{ B.length next = 1 } -> linked_list

let main () =
  C.exit_success
