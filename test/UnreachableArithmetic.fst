module UnreachableArithmetic

module U32 = FStar.UInt32

(* Keep the booleans until KaRaMeL inlines the local bindings, and expose
   zero divisors by substituting the helpers. F* verifies that the arithmetic
   is unreachable; substituting zero directly here would make F* reduce it. *)
[@ "substitute" ]
let and_div_aux (x: U32.t) : bool =
  [@@CInline] let b = false in
  b && U32.div 1ul x = 0ul

[@ "substitute" ]
let or_div_aux (x: U32.t) : bool =
  [@@CInline] let b = true in
  b || U32.div 1ul x = 0ul

(* The comparison stays nonliteral during constant folding, so the
   arithmetic must remain unfolded even though its branch is unreachable. *)
[@ "substitute" ]
let guarded_div_aux (x: U32.t) : U32.t =
  if x <> 0ul then U32.div 1ul x else 2ul

let and_div () : bool = and_div_aux 0ul
let or_div () : bool = or_div_aux 0ul
let guarded_div () : U32.t = guarded_div_aux 0ul

let live_div () : bool =
  [@@CInline] let b = true in
  [@@CInline] let two = 2ul in
  b && U32.div 6ul two = 0ul

[@ "substitute" ]
let and_mod_aux (x: U32.t) : bool =
  [@@CInline] let b = false in
  b && U32.rem 1ul x = 0ul

[@ "substitute" ]
let or_mod_aux (x: U32.t) : bool =
  [@@CInline] let b = true in
  b || U32.rem 1ul x = 0ul

[@ "substitute" ]
let guarded_mod_aux (x: U32.t) : U32.t =
  if x <> 0ul then U32.rem 1ul x else 2ul

let and_mod () : bool = and_mod_aux 0ul
let or_mod () : bool = or_mod_aux 0ul
let guarded_mod () : U32.t = guarded_mod_aux 0ul

let live_mod () : bool =
  [@@CInline] let b = true in
  [@@CInline] let two = 2ul in
  b && U32.rem 6ul two = 0ul

let main () : FStar.Int32.t =
  if not (and_div ()) && or_div () && guarded_div () = 2ul && not (live_div ())
  && not (and_mod ()) && or_mod () && guarded_mod () = 2ul && live_mod ()
  then 0l
  else 1l
