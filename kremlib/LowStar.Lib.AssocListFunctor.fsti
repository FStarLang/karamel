module LowStar.Lib.AssocListFunctor

/// A Low*, stateful associative list functor that exposes a map-like interface.
/// Same as LowStar.Lib.AssocList but wrapped in a functor.x

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

// TODO: share this definition with LowStar.Lib.AssocList
inline_for_extraction noextract
let map (k: eqtype) v =
  M.t k (option v)

inline_for_extraction noextract
noeq type assoc_list = | AssocList :
  t: (eqtype -> Type0 -> Type0) ->

  v: (#t_k:eqtype -> #t_v:Type0 -> h:HS.mem -> ll:t t_k t_v -> GTot (map t_k t_v)) ->

  invariant: (#t_k:eqtype -> #t_v:Type0 -> h:HS.mem -> ll:t t_k t_v -> Type0) ->

  region_of: (#t_k:eqtype -> #t_v:Type0 -> ll:t t_k t_v -> GTot B.loc) ->

  frame: (#t_k:eqtype -> #t_v:Type0 -> ll:t t_k t_v -> l:B.loc -> h0:HS.mem -> h1: HS.mem -> Lemma
    (requires
      invariant h0 ll /\
      B.loc_disjoint l (region_of ll) /\
      B.modifies l h0 h1)
    (ensures
      invariant h1 ll /\
      v h1 ll == v h0 ll)
    [ SMTPatOr [
        [ SMTPat (invariant h1 ll); SMTPat (B.modifies l h0 h1) ];
        [ SMTPat (v h1 ll); SMTPat (B.modifies l h0 h1) ];
      ]]) ->

  create_in: (#t_k:eqtype -> #t_v:Type -> r:HS.rid -> ST (t t_k t_v)
    (requires fun h0 ->
      ST.is_eternal_region r)
    (ensures fun h0 ll h1 ->
      invariant h1 ll /\
      B.(modifies loc_none h0 h1) /\
      v h1 ll == M.const None /\
      region_of ll == B.(loc_all_regions_from false r))) ->

  find: (#t_k: eqtype -> #t_v: Type0 -> ll: t t_k t_v -> k: t_k ->
  Stack (option t_v)
    (requires fun h0 ->
      invariant h0 ll)
    (ensures fun h0 x h1 ->
      let m: map t_k t_v = v h0 ll in
      h0 == h1 /\
      x == M.sel m k)) ->

  add: (#t_k: eqtype -> #t_v: Type0 -> ll: t t_k t_v -> k: t_k -> x: t_v ->
  ST unit
    (requires fun h0 ->
      invariant h0 ll)
    (ensures fun h0 _ h1 ->
      B.modifies (region_of ll) h0 h1 /\
      invariant h1 ll /\
      v h1 ll == M.upd (v h0 ll) k (Some x))) ->

  remove_all: (#t_k: eqtype -> #t_v: Type0 -> ll: t t_k t_v -> k: t_k ->
  ST unit
    (requires fun h0 ->
      invariant h0 ll)
    (ensures fun h0 _ h1 ->
      B.modifies (region_of ll) h0 h1 /\
      invariant h1 ll /\
      v h1 ll == M.upd (v h0 ll) k None)) ->

  clear: (#t_k: eqtype -> #t_v: Type0 -> ll: t t_k t_v ->
  ST unit
    (requires fun h0 ->
      invariant h0 ll)
    (ensures fun h0 _ h1 ->
      B.modifies (region_of ll) h0 h1 /\
      invariant h1 ll /\
      v h1 ll == M.const None)) ->

  free: (#t_k: eqtype -> #t_v: Type0 -> ll: t t_k t_v ->
  ST unit
    (requires fun h0 ->
      invariant h0 ll)
    (ensures fun h0 _ h1 ->
      B.modifies (region_of ll) h0 h1)) ->
  
  assoc_list
