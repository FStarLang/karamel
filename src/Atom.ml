type t = int
  [@@deriving yojson,show]

let r = ref 0

let fresh () =
  incr r;
  !r

let equal = (=)
