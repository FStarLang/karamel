module PatternAny

module I32 = FStar.Int32

type role = | Client | Server

type id =
| ID12: role -> id

// Returns the local nonce
let nonce_of_id (i : id) : I32.t =
  match i with
  | ID12 rw -> if rw = Client then 0l else 1l

let main () =
  nonce_of_id (ID12 Client)
