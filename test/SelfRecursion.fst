module SelfRecursion

module U32 = FStar.UInt32

(* Self-recursion does not require a prototype in an internal header. *)
private let rec local (n: U32.t) : Tot U32.t (decreases (U32.v n)) =
  if n = 0ul then 0ul
  else U32.add_mod (local (U32.sub n 1ul)) 1ul

let entry (n: U32.t) : U32.t = local n

(* Public recursion must remain public. *)
let rec public_rec (n: U32.t) : Tot U32.t (decreases (U32.v n)) =
  if n = 0ul then 0ul
  else U32.add_mod (public_rec (U32.sub n 1ul)) 1ul

(* Mutual recursion still needs a forward declaration. *)
private let rec mutual_first (n: U32.t) : Tot U32.t (decreases (U32.v n)) =
  if n = 0ul then 0ul
  else U32.add_mod (mutual_second (U32.sub n 1ul)) 1ul

and mutual_second (n: U32.t) : Tot U32.t (decreases (U32.v n)) =
  if n = 0ul then 0ul
  else U32.add_mod (mutual_first (U32.sub n 1ul)) 1ul

let mutual_entry (n: U32.t) : U32.t = mutual_first n

let main () = 0l
