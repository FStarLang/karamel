module RingBuffer

/// This module demonstrates how to implement a ringbuffer in Low*. It uses the
/// new LowStar.Buffer abstraction, and demonstrates how to separate functional
/// predicates from their low-level stateful counterparts.
///
/// TODO: add ``push_back`` and ``pop_back``

/// We define the canonical abbreviations, taking care to shadow ST to make sure
/// we don't end up referring to FStar.ST by accident.
module B = LowStar.Buffer
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module M = LowStar.Modifies
module ST = FStar.HyperStack.ST
module S = FStar.Seq

/// This brings into scope the ``!*`` and ``*=`` operators, which are
/// specifically designed to operate on buffers of size 1, i.e. on pointers.
open LowStar.BufferOps
open FStar.HyperStack.ST

/// A ringbuffer is a view over a buffer, with a start index, a length (i.e. how
/// many elements are currently being stored) and a total length (i.e. the size
/// of the underlying ``b``). We chose this style, as opposed to a pair of
/// ``first`` and ``last`` indices, because it avoids modular arithmetic which
/// would be difficult to reason about.
noeq
type t a = {
  b: B.buffer a;
  first: B.pointer U32.t;
  length: B.pointer U32.t;
  total_length: U32.t
}

/// To facilitate writing predicates, we define a handy shortcut that is the
/// reflection of the ``!*`` operator at the proof level.
unfold
let deref #a (h: HS.mem) (x: B.pointer a) = B.get h x 0

/// A first version of the well-formedness predicate for ring buffers. This
/// predicate refers to a sequence, not a buffer, and therefore does not need
/// the memory. It is useful in this module to have two versions of predicates:
/// one that takes into account the memory, disjointness, etc. and another one
/// that only focuses on index arithmetic. Nothing surprising here. Note that
/// zero-sized ringbuffers are not allowed.
let well_formed_f #a (b: S.seq a) (first length total_length: U32.t) =
  let open U32 in
  S.length b = v total_length /\
  length <=^ total_length /\
  first <^ total_length /\
  total_length >^ 0ul

/// Same predicate as above, but this time operating on a memory state and using
/// a stateful ringbuffer.
let well_formed #a (h: HS.mem) (x: t a) =
  B.live h x.b /\ B.live h x.first /\ B.live h x.length /\
  M.(loc_disjoint (loc_buffer x.b) (loc_buffer x.first)) /\
  M.(loc_disjoint (loc_buffer x.b) (loc_buffer x.length)) /\
  M.(loc_disjoint (loc_buffer x.first) (loc_buffer x.length)) /\
  well_formed_f (B.as_seq h x.b) (deref h x.first) (deref h x.length) x.total_length

/// We next define operators for moving around the ringbuffer with wraparound
/// semantics. Defining this using a modulo operator is not a good idea, because:
/// - writing ``i +^ 1ul %^ total_length`` may overflow
/// - Z3 is notoriously bad at reasoning with modular arithmetic.
/// So, instead, we just do a simple branch.
let next (i total_length: U32.t): Pure U32.t
  (requires U32.(total_length >^ 0ul /\ i <^ total_length))
  (ensures fun r -> U32.( r <^ total_length ))
=
  let open U32 in
  if i =^ total_length -^ 1ul then
    0ul
  else
    i +^ 1ul

let prev (i total_length: U32.t): Pure U32.t
  (requires U32.(total_length >^ 0ul /\ i <^ total_length))
  (ensures fun r -> U32.( r <^ total_length ))
=
  let open U32 in
  if i >^ 0ul then
    i -^ 1ul
  else
    total_length -^ 1ul

/// These two are useful from the client's perspective, to capture how many slots
/// are left in the buffer.
let remaining_space #a (h: HS.mem) (x: t a { well_formed h x }) =
  U32.( x.total_length -^ (deref h x.length) )

let space_left #a (h: HS.mem) (x: t a { well_formed h x }) =
  U32.( remaining_space h x >^ 0ul )

/// A predicate over indices that captures whether a given entry in the buffer
/// is occupied. Once again, we avoid modular arithmetic by branching.
let used_slot_f (first length total_length i: U32.t) =
  let first = U32.v first in
  let length = U32.v length in
  let total_length = U32.v total_length in
  let i = U32.v i in
  first <= i /\ i < first + length \/
  first <= i + total_length /\ i + total_length < first + length

/// Same thing, but over a memory and the actual references.
let used_slot #a (h: HS.mem) (x: t a { well_formed h x }) (i: U32.t) =
  let first = deref h x.first in
  let length = deref h x.length in
  let total_length = x.total_length in
  used_slot_f first length total_length i

/// We reflect a ringbuffer as a list. This is the functional version that
/// operates over a sequence.
let rec as_list_f #a
  (b: S.seq a)
  (first length total_length: U32.t): Ghost (list a)
    (requires well_formed_f b first length total_length)
    (ensures fun _ -> True)
    (decreases (U32.v length))
=
  if U32.( length =^ 0ul ) then
    []
  else
    S.index b (U32.v first) ::
      as_list_f b (next first total_length) U32.( length -^ 1ul ) total_length

/// The one central lemma of this module: assigning something in the unused
/// parts of the buffer does not affect the contents of the list.
let rec seq_update_unused_preserves_list (#a: eqtype)
  (b: S.seq a)
  (i: U32.t)
  (e: a)
  (first length total_length: U32.t): Lemma
  (requires
    U32.v i < S.length b /\
    well_formed_f b first length total_length /\
     ~(used_slot_f first length total_length i))
  (ensures
    well_formed_f b first length total_length /\ (
    let b' = S.upd b (U32.v i) e in
    as_list_f b first length total_length = as_list_f b' first length total_length
  ))
  (decreases (U32.v length))
=
  if U32.(length =^ 0ul) then
    ()
  else begin
    seq_update_unused_preserves_list b i e (next first total_length)
      U32.(length -^ 1ul) total_length
  end

/// This version is more convenient and refers to the current memory and buffer,
/// as opposed to as sequence.
let as_list #a (h: HS.mem) (x: t a): Ghost (list a)
  (requires well_formed h x)
  (ensures fun _ -> True)
=
  as_list_f (B.as_seq h x.b) (deref h x.first) (deref h x.length) x.total_length

/// ``pop`` is easy to prove, and requires no particular call to a lemma,
/// because we don't modify the underlying buffer. Since the buffer contents
/// don't change, the total predicate ``as_list_f`` is preserved, and F* is able
/// to prove automatically the functional specification.
let pop (#a: eqtype) (x: t a): Stack a
  (requires fun h ->
    well_formed h x /\ U32.(deref h x.length >^ 0ul))
  (ensures fun h0 r h1 ->
    well_formed h1 x /\
    M.(modifies (loc_union (loc_buffer x.length) (loc_buffer x.first)) h0 h1) /\
    U32.(remaining_space h1 x = remaining_space h0 x +^ 1ul) /\ (
    let hd :: tl = as_list h0 x in
    r = hd /\ as_list h1 x = tl))
=
  let e = x.b.(!*x.first) in
  let h0 = ST.get () in
  x.first *= next !*x.first x.total_length;
  x.length *= U32.(!*x.length -^ 1ul);
  let h1 = ST.get () in
  e

/// ``push`` is slightly more involved and crucially relies on the lemma above.
let push (#a: eqtype) (x: t a) (e: a): Stack unit
  (requires fun h ->
    well_formed h x /\ space_left h x)
  (ensures fun h0 _ h1 ->
    well_formed h1 x /\
    U32.(remaining_space h1 x =^ remaining_space h0 x -^ 1ul) /\
    M.(modifies (loc_union
      (loc_buffer x.length)
        (loc_union (loc_buffer x.first) (loc_buffer x.b))) h0 h1) /\
    as_list h1 x = e :: as_list h0 x)
=
  let dest_slot = prev !*x.first x.total_length in
  let h0 = ST.get () in
  x.b.(dest_slot) <- e;
  seq_update_unused_preserves_list (B.as_seq h0 x.b) dest_slot e
    (deref h0 x.first) (deref h0 x.length) x.total_length;
  x.first *= dest_slot;
  x.length *= U32.(!*x.length +^ 1ul)

/// ``create`` leverages the ``StackInline`` effect, and allocates three buffers
/// -- we encapsulate stack allocation in a separate function, which facilitates
/// verification. Relying on KreMLin's support, ``create`` will be textually
/// inlined at call-site so that the allocations are effectively in the caller's
/// stack frame.
let create (#a: eqtype) (init: a) (len: U32.t): StackInline (t a)
  (requires (fun _ -> U32.v len > 0))
  (ensures (fun h0 x h1 ->
     well_formed h1 x /\ remaining_space h1 x = len))
=
  let b = B.alloca init len in
  { b = b; first = B.alloca 0ul 1ul; length = B.alloca 0ul 1ul; total_length = len }

/// This test is crafted for continuous integration, so that the return value is
/// 0l, indicating success.
let main (): St Int32.t =
  push_frame ();
  let rb = create 1l 32ul in
  push rb 0l;
  let r = pop rb in
  pop_frame ();
  r
