exception Error of string

let throw_error fmt =
  Printf.ksprintf (fun msg -> raise (Error msg)) fmt
