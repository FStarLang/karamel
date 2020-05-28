module LowStar.Lib.AssocList

/// A Low*, stateful associative list that exposes a map-like interface.

module B = LowStar.Buffer
module HS = FStar.HyperStack
module G = FStar.Ghost
module L = FStar.List.Tot
module U32 = FStar.UInt32
module ST = FStar.HyperStack.ST

module M = FStar.Map
module LL2 = LowStar.Lib.LinkedList2
module LL1 = LowStar.Lib.LinkedList

open FStar.HyperStack.ST
open LowStar.BufferOps

/// Types, invariants, footprint
/// ----------------------------

val t: eqtype -> Type0 -> Type0

/// Rather than force clients to provide a dummy value for the type (which would
/// allow us to do something like initialize an empty map with ``restrict (const
/// default)``, we use an option.
let map (k: eqtype) v =
  M.t k (option v)

/// Reflecting a stateful, imperative map as a functional one in a given heap.
val v: #t_k:eqtype -> #t_v:Type0 -> h:HS.mem -> ll:t t_k t_v -> GTot (map t_k t_v)

val invariant: #t_k:eqtype -> #t_v:Type0 -> h:HS.mem -> ll:t t_k t_v -> Type0

val footprint: #t_k:eqtype -> #t_v:Type0 -> h:HS.mem -> ll:t t_k t_v -> Ghost B.loc
  (requires invariant h ll)
  (ensures fun _ -> True)

val region_of: #t_k:eqtype -> #t_v:Type0 -> ll:t t_k t_v -> GTot B.loc

val frame: #t_k:eqtype -> #t_v:Type0 -> ll:t t_k t_v -> l:B.loc -> h0:HS.mem -> h1: HS.mem -> Lemma
  (requires
    invariant h0 ll /\
    B.loc_disjoint l (region_of ll) /\
    B.modifies l h0 h1)
  (ensures
    invariant h1 ll /\
    footprint h1 ll == footprint h0 ll /\
    v h1 ll == v h0 ll)
  [ SMTPatOr [
      [ SMTPat (invariant h1 ll); SMTPat (B.modifies l h0 h1) ];
      [ SMTPat (footprint h1 ll); SMTPat (B.modifies l h0 h1) ];
      [ SMTPat (v h1 ll); SMTPat (B.modifies l h0 h1) ];
    ]]

val footprint_in_r: #t_k:eqtype -> #t_v:Type0 -> h0:HS.mem -> ll:t t_k t_v -> Lemma
  (requires
    invariant h0 ll)
  (ensures
    B.(loc_includes (region_of ll) (footprint h0 ll)))
  [ SMTPat (footprint h0 ll) ]

/// Creating an imperative map
/// --------------------------

val create_in: #t_k:eqtype -> #t_v:Type -> r:HS.rid -> ST (t t_k t_v)
  (requires fun h0 ->
    ST.is_eternal_region r)
  (ensures fun h0 ll h1 ->
    invariant h1 ll /\
    B.(modifies loc_none h0 h1) /\
    B.fresh_loc (footprint h1 ll) h0 h1 /\
    v h1 ll == M.const None /\
    region_of ll == B.(loc_all_regions_from true r))


/// Find
/// ----

val find (#t_k: eqtype) (#t_v: Type0) (ll: t t_k t_v) (k: t_k):
  Stack (option t_v)
    (requires fun h0 ->
      invariant h0 ll)
    (ensures fun h0 x h1 ->
      let m: map t_k t_v = v h0 ll in
      h0 == h1 /\
      x == M.sel m k)

/// Adding elements
/// ---------------

val add (#t_k: eqtype) (#t_v: Type0) (ll: t t_k t_v) (k: t_k) (x: t_v):
  ST unit
    (requires fun h0 ->
      invariant h0 ll)
    (ensures fun h0 _ h1 ->
      B.modifies (footprint h0 ll) h0 h1 /\
      invariant h1 ll /\
      v h1 ll == M.upd (v h0 ll) k (Some x))

/// Removing elements
/// -----------------

val remove_all (#t_k: eqtype)
  (#t_v: Type0)
  (ll: t t_k t_v)
  (k: t_k):
  ST unit
    (requires fun h0 ->
      invariant h0 ll)
    (ensures fun h0 _ h1 ->
      B.modifies (footprint h0 ll) h0 h1 /\
      invariant h1 ll /\
      v h1 ll == M.upd (v h0 ll) k None)

/// Clearing (resetting)
/// --------------------

val clear (#t_k: eqtype)
  (#t_v: Type0)
  (ll: t t_k t_v):
  ST unit
    (requires fun h0 ->
      invariant h0 ll)
    (ensures fun h0 _ h1 ->
      B.modifies (footprint h0 ll) h0 h1 /\
      invariant h1 ll /\
      v h1 ll == M.const None)

/// Freeing the resource
/// --------------------

val free (#t_k: eqtype)
  (#t_v: Type0)
  (ll: t t_k t_v):
  ST unit
    (requires fun h0 ->
      invariant h0 ll)
    (ensures fun h0 _ h1 ->
      B.modifies (footprint h0 ll) h0 h1)
