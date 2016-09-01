let must = function
  | Some x -> x
  | None -> raise (Invalid_argument "Option.must")
