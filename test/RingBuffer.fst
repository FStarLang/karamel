module RingBuffer

module B = LowStar.Buffer
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module M = LowStar.Modifies
module ST = FStar.HyperStack.ST

open LowStar.BufferOps
open FStar.HyperStack.ST

noeq
type t a = {
  b: B.buffer a;
  first: B.pointer U32.t;
  length: B.pointer U32.t;
  total_length: U32.t
}

// Some helpers...
unfold
let deref #a h (x: B.pointer a) = B.get h x 0

let well_formed_f #a (h: HS.mem) (b: B.buffer a) (first length total_length: U32.t) =
  let open U32 in
  B.length b = v total_length /\
  length <=^ total_length /\
  first <^ total_length /\
  total_length >^ 0ul

let well_formed #a (h: HS.mem) (x: t a) =
  B.live h x.b /\ B.live h x.first /\ B.live h x.length /\
  M.(loc_disjoint (loc_buffer x.b) (loc_buffer x.first)) /\
  M.(loc_disjoint (loc_buffer x.b) (loc_buffer x.length)) /\
  M.(loc_disjoint (loc_buffer x.first) (loc_buffer x.length)) /\
  well_formed_f h x.b (deref h x.first) (deref h x.length) x.total_length

// Avoiding the modulo operator at all costs; also: can't use !*x.first +
// x.total_length -^ 1ul %^ x.total_length because this might overflow!
let prev (i total_length: U32.t): Pure U32.t
  (requires U32.(total_length >^ 0ul /\ i <^ total_length))
  (ensures fun r -> U32.( r <^ total_length ))
=
  let open U32 in
  if i >^ 0ul then
    i -^ 1ul
  else
    total_length -^ 1ul

let next (i total_length: U32.t): Pure U32.t
  (requires U32.(total_length >^ 0ul /\ i <^ total_length))
  (ensures fun r -> U32.( r <^ total_length ))
=
  let open U32 in
  if i =^ total_length -^ 1ul then
    0ul
  else
    i +^ 1ul

let rec as_list_aux #a
  (h: HS.mem)
  (b: B.buffer a)
  (first length total_length: U32.t): Ghost (list a)
    (requires well_formed_f h b first length total_length)
    (ensures fun _ -> True)
    (decreases (U32.v length))
=
  if U32.( length =^ 0ul ) then
    []
  else
    B.get h b (U32.v first) ::
      as_list_aux h b (next first total_length) U32.( length -^ 1ul ) total_length

let as_list #a (h: HS.mem) (x: t a): Ghost (list a)
  (requires well_formed h x)
  (ensures fun _ -> True)
=
  as_list_aux h x.b (deref h x.first) (deref h x.length) x.total_length

let remaining_space #a (h: HS.mem) (x: t a { well_formed h x }) =
  U32.( x.total_length -^ (deref h x.length) )

let space_left #a (h: HS.mem) (x: t a { well_formed h x }) =
  U32.( remaining_space h x >^ 0ul )

let used_slot #a (h: HS.mem) (x: t a { well_formed h x }) (i: U32.t) =
  let first = U32.v (deref h x.first) in
  let length = U32.v (deref h x.length) in
  let total_length = U32.v x.total_length in
  let i = U32.v i in
  first <= i /\ i < first + length \/
  first <= i + total_length /\ i + total_length < first + length

let push (#a: eqtype) (x: t a) (e: a): Stack unit
  (requires fun h ->
    well_formed h x /\ space_left h x)
  (ensures fun h0 _ h1 ->
    well_formed h1 x /\
    U32.(remaining_space h1 x =^ remaining_space h0 x -^ 1ul) /\
    M.(modifies (loc_union
      (loc_buffer x.length)
        (loc_union (loc_buffer x.first) (loc_buffer x.b))) h0 h1) /\
    True) // as_list h1 x = e :: as_list h0 x)
=
  let dest_slot = prev !*x.first x.total_length in
  x.b.(dest_slot) <- e;
  x.first *= dest_slot;
  x.length *= U32.(!*x.length +^ 1ul)

let pop (#a: eqtype) (x: t a): Stack a
  (requires fun h ->
    well_formed h x /\ U32.(deref h x.length >^ 0ul))
  (ensures fun h0 r h1 ->
    well_formed h1 x /\
    M.(modifies (loc_union (loc_buffer x.length) (loc_buffer x.first)) h0 h1) /\
    U32.(remaining_space h1 x = remaining_space h0 x +^ 1ul) /\ (
    let hd :: tl = as_list h0 x in
    r = hd))// /\ as_list h1 x = tl))
=
  let e = x.b.(!*x.first) in
  x.first *= next !*x.first x.total_length;
  x.length *= U32.(!*x.length -^ 1ul);
  e

let create (#a: eqtype) (init: a) (len: U32.t): StackInline (t a)
  (requires (fun _ -> U32.v len > 0))
  (ensures (fun h0 x h1 ->
     well_formed h1 x /\ remaining_space h1 x = len))
=
  let b = B.alloca init len in
  { b = b; first = B.alloca 0ul 1ul; length = B.alloca 0ul 1ul; total_length = len }

let main (): St Int32.t =
  push_frame ();
  let rb = create 1l 32ul in
  push rb 0l;
  let r = pop rb in
  pop_frame ();
  r
