type t = unit ref
  [@@deriving yojson]

let fresh () = ref ()

let equal = (==)
