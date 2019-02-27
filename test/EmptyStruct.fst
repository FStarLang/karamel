module EmptyStruct

noeq
type t =
  | T: Ghost.erased int -> t

noeq
type u =
  | U: UInt32.t -> u

noeq
type v = { x: UInt32.t }

let main () =
  0l
