let must = function
  | Some x -> x
  | None -> raise (Invalid_argument "Option.must")

let map f = function
  | Some x -> Some (f x)
  | None -> None
