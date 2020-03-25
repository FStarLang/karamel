/// Auxiliary implementation lemmas
/// ===============================

module Impl.Bignum.Lemmas

/// Let's move lemmas to a separate module. It'll be cleaner!

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq

module U32 = FStar.UInt32
module U64 = FStar.UInt64

/// I oftentimes use ``Spec`` to refer to the spec of the current module.
module Spec = Spec.Bignum

/// This module only contains operators, and is meant to be opened.
open LowStar.BufferOps
open FStar.HyperStack.ST

#set-options "--max_fuel 0 --max_ifuel 0"


/// This is my little library of sequence lemmas that I always carry with me.
let lemma_slice (#a: Type) (s: S.seq a) (i: nat): Lemma
  (requires (i <= S.length s))
  (ensures (S.equal (S.append (S.slice s 0 i) (S.slice s i (S.length s))) s))
=
  ()

let lemma_slice_ijk (#a: Type) (s: S.seq a) (i j k: nat): Lemma
  (requires (i <= j /\ j <= k /\ k <= S.length s))
  (ensures (S.equal (S.append (S.slice s i j) (S.slice s j k)) (S.slice s i k)))
=
  ()

#push-options "--fuel 1"
let v_zero_tail (x: Spec.t): Lemma
  (requires Spec.v x = 0 /\ S.length x > 0)
  // Two notes:
  // i) discrepancy between B.sub that takes a length as its last argument and
  //    S.slice that takes an index
  // ii) doing this in terms of slice since the spec of sub is in terms of
  //     slice; using tail would require lemma_tl all over again
  (ensures Spec.v (S.slice x 1 (S.length x)) = 0)
=
  ()

let rec v_all_zeroes (x: Spec.t): Lemma
  (requires x `S.equal` S.create (S.length x) 0ul)
  (ensures Spec.v x == 0)
  (decreases (S.length x))
=
  if S.length x = 0 then
    ()
  else
    v_all_zeroes (S.tail x)
#pop-options

let lemma_empty #a (x: S.seq a): Lemma
  (requires S.length x = 0)
  (ensures x `S.equal` S.empty)
=
  ()

let max32 (x y: U32.t): U32.t =
  if x `U32.gt` y then x else y

let max_fact (z x y: U32.t): Lemma
  (requires U32.(
    x >^ 0ul /\ y >^ 0ul /\ z >^ 0ul /\
    U32.v z == U32.v (max32 x y) + 1))
  (ensures
    U32.(v (z -^ 1ul) == U32.v (max32 (x -^ 1ul) (y -^ 1ul)) + 1))
=
  ()

let slice_create #a (i: nat) (s: S.seq a): Lemma
  (requires S.length s > 0 /\ i + 1 < S.length s)
  (ensures S.slice s i (i + 1) `S.equal` S.create 1 (S.index s i))
=
  ()
