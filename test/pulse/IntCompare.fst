module IntCompare

module U32 = FStar.UInt32
module F32 = FStar.Float32

assume val consume : bool -> Dv unit
assume val next : unit -> Dv U32.t

let comparisons (x y : U32.t) (z : F32.t) =
  consume (U32.eq x x);
  consume (not (U32.eq x x));
  consume (U32.lt x x);
  consume (U32.lte x x);
  consume (U32.gt x x);
  consume (U32.gte x x);
  (* Different variables and floating-point comparisons must remain. *)
  consume (U32.eq x y);
  consume (F32.ieee_eq z z);
  consume (not (F32.ieee_eq z z));
  consume (F32.lt z z);
  consume (F32.lte z z)

let expressions (x y : U32.t) =
  consume (U32.eq (U32.add_mod x 1ul) (U32.add_mod x 1ul));
  consume (not (U32.eq (U32.add_mod x 1ul) (U32.add_mod x 1ul)));
  consume (U32.lt (U32.add_mod x 1ul) (U32.add_mod x 1ul));
  consume (U32.lte (U32.add_mod x 1ul) (U32.add_mod x 1ul));
  consume (U32.gt (U32.add_mod x 1ul) (U32.add_mod x 1ul));
  consume (U32.gte (U32.add_mod x 1ul) (U32.add_mod x 1ul));
  (* Simplify the operands before comparing them. *)
  consume (U32.eq (U32.add_mod x 0ul) x);
  (* Similar expressions with different operands must remain. *)
  consume (U32.eq (U32.add_mod x 1ul) (U32.add_mod y 1ul));
  consume (U32.lt (U32.add_mod x 1ul) (U32.add_mod x 2ul))

let select (x : U32.t) =
  [@@CInline] let y = if U32.eq x x then x else 0ul in
  U32.add_mod y 1ul

let select_false (x : U32.t) =
  if not (U32.eq x x) then 0ul else U32.add_mod x 1ul

let calls () =
  (* Both calls must be evaluated and their results compared. *)
  consume (U32.eq (next ()) (next ()));
  consume (not (U32.eq (next ()) (next ())));
  consume (U32.lt (next ()) (next ()));
  consume (U32.lte (next ()) (next ()));
  consume (U32.gt (next ()) (next ()));
  consume (U32.gte (next ()) (next ()))

let nested_calls () =
  consume (U32.eq (U32.add_mod (next ()) 1ul) (U32.add_mod (next ()) 1ul));
  consume (U32.lt (U32.add_mod (next ()) 1ul) (U32.add_mod (next ()) 1ul))
