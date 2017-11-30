let must = function
  | Some x -> x
  | None -> raise (Invalid_argument "Option.must")

let map f = function
  | Some x -> Some (f x)
  | None -> None

let map_or f o d =
  match o with
  | Some x -> f x
  | None -> d

let or_empty = function
  | Some x -> x
  | None -> ""
