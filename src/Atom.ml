type t = unit ref
  [@@deriving yojson, show, visitors { variety = "iter"; monomorphic = [ "env" ] }]

let fresh () = ref ()

let equal = (==)
