exception Error of string

let throw_error fmt =
  Printf.kbprintf (fun buf -> raise (Error (Buffer.contents buf))) (Buffer.create 16) fmt
