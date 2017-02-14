type t = unit ref
  [@@deriving yojson,show]

let fresh () = ref ()

let equal = (==)
