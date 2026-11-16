module NegatedEquality

module U32 = FStar.UInt32
module U8 = FStar.UInt8
module I32 = FStar.Int32
module B = LowStar.Buffer
open FStar.HyperStack.ST

let uint_ne (a b: U32.t) = not (a = b)
let uint_eq (a b: U32.t) = not (a <> b)
let bool_ne (a b: bool) = not (a = b)
let double_not (a b: U32.t) = not (not (a = b))
let bool_double_not (c: bool) = not (not c)

(* Constant folding can itself introduce negations when reducing ternaries. *)
let conditional_not (a b: U32.t) = if a = b then false else true
let conditional_and (a b: U32.t) (c: bool) = if a = b then false else c
let conditional_or (a b: U32.t) (c: bool) = if a = b then c else true

(* Complement ordering comparisons on signed and unsigned integers. *)
let uint_ge (a b: U32.t) = not (U32.lt a b)
let uint_gt (a b: U32.t) = not (U32.lte a b)
let uint_le (a b: U32.t) = not (U32.gt a b)
let uint_lt (a b: U32.t) = not (U32.gte a b)
let int_ge (a b: I32.t) = not (I32.lt a b)
let int_gt (a b: I32.t) = not (I32.lte a b)
let int_le (a b: I32.t) = not (I32.gt a b)
let int_lt (a b: I32.t) = not (I32.gte a b)

(* Preserve the truncation of narrow arithmetic. *)
let narrow_ne (a b: U8.t) = not (U8.add_mod a b = 0uy)
let narrow_ge (a b c: U8.t) = not (U8.lt (U8.add_mod a b) c)

(* Null tests exercise polymorphic comparisons. *)
let nonnull (p: B.buffer U32.t): Stack bool
  (fun h -> B.live h p) (fun _ _ _ -> True) =
  not (B.is_null p)

let null_again (p: B.buffer U32.t): Stack bool
  (fun h -> B.live h p) (fun _ _ _ -> True) =
  not (not (B.is_null p))

let configured (p: B.buffer U32.t) (enabled: bool): Stack bool
  (fun h -> B.live h p) (fun _ _ _ -> True) =
  not (B.is_null p) = enabled

(* Empty then branches introduce negation during Simplify. *)
let null_else (p: B.pointer_or_null U32.t): Stack unit
  (fun h -> B.live h p) (fun _ _ _ -> True) =
  if B.is_null p then () else B.upd p 0ul 7ul

let nonnull_else (out: B.pointer U32.t) (p: B.buffer U32.t): Stack unit
  (fun h -> B.live h out /\ B.live h p) (fun _ _ _ -> True) =
  if not (B.is_null p) then () else B.upd out 0ul 7ul

let next (p: B.pointer U32.t): Stack U32.t
  (fun h -> B.live h p)
  (fun h0 _ h1 -> B.modifies (B.loc_buffer p) h0 h1) =
  let n = U32.add_mod (B.index p 0ul) 1ul in
  B.upd p 0ul n;
  n

(* Complementing equality must preserve both effectful calls. *)
let call_ne (p: B.pointer U32.t): Stack bool
  (fun h -> B.live h p)
  (fun h0 _ h1 -> B.modifies (B.loc_buffer p) h0 h1) =
  let a = next p in
  let b = next p in
  not (a = b)

let main (): Stack Int32.t (fun _ -> True) (fun _ _ _ -> True) =
  push_frame ();
  let p = B.alloca 0ul 1ul in
  let distinct = call_ne p in
  let count = B.index p 0ul in
  pop_frame ();
  if distinct && count = 2ul then 0l else 1l
