type t = int
  [@@deriving yojson, show, visitors { variety = "iter"; monomorphic = [ "env" ] }]

let r = ref 0

let fresh () =
  incr r;
  !r

let equal = (=)
