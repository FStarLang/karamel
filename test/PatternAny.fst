module PatternAny

module I32 = FStar.Int32

type role = | Client | Server

type id =
| ID12: role -> id

// Returns the local nonce
let nonce_of_id (i : id) : I32.t =
  match i with
  | ID12 rw -> match rw with Client -> 0l | _ -> 1l

let main () =
  nonce_of_id (ID12 Client)
