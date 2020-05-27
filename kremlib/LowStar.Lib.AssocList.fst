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

#set-options "--fuel 0 --ifuel 0"

/// We prefer the packed representation that is in general easier to use and will
/// look at the underlying predicate-based representation from LL1 only when
/// strictly needed.
val t: eqtype -> Type0 -> Type0
let t k v =
  LL2.t (k & v)

/// Rather than force clients to provide a dummy value for the type (which would
/// allow us to do something like initialize an empty map with ``restrict (const
/// default)``, we use an option.
val map: eqtype -> Type0 -> Type0
let map k v =
  M.t k (option v)

/// Functions suffixed with an underscore operate on either LL1 or raw lists
/// while those without operate on LL2.
val v_: #t_k:eqtype -> #t_v:Type0 -> l:list (t_k & t_v) -> GTot (map t_k t_v)
let v_ #_ #t_v l =
  List.Tot.fold_right (fun (k, v) m -> M.upd m k (Some v)) l (M.const (None #t_v))

/// Reflecting a stateful, imperative map as a functional one in a given heap.
val v: #t_k:eqtype -> #t_v:Type0 -> h:HS.mem -> ll:t t_k t_v -> GTot (map t_k t_v)
let v #_ #_ h ll =
  let l = LL2.v h ll in
  v_ l

val invariant: #t_k:eqtype -> #t_v:Type0 -> h:HS.mem -> ll:t t_k t_v -> Type0
let invariant #_ #_ h ll =
  LL2.invariant h ll

val footprint: #t_k:eqtype -> #t_v:Type0 -> h:HS.mem -> ll:t t_k t_v -> Ghost B.loc
  (requires invariant h ll)
  (ensures fun _ -> True)
let footprint #_ #_ h ll =
  LL2.footprint h ll

/// What's the best way for clients to reason about this? Maybe a lemma that says:
///
/// B.(loc_disjoint l (loc_all_regions_from true r)) ==> B.(loc_disjoint l (footprint h ll))
///
/// This would allow clients to deduce that their own allocations are disjoint from the footprint of this. And also to apply the framing lemma with proper patterns!

/// Proper recursion can only be done over the LL1.t type (unpacked representation).
val find_ (#t_k: eqtype) (#t_v: Type0) (hd: LL1.t (t_k & t_v)) (l: G.erased (list (t_k & t_v))) (k: t_k):
  Stack (option t_v)
    (requires fun h0 ->
      LL1.well_formed h0 hd l /\
      LL1.invariant h0 hd l)
    (ensures fun h0 x h1 ->
      let m: map t_k t_v = v_ l in
      h0 == h1 /\
      x == M.sel m k)

#push-options "--fuel 1 --ifuel 1"
let rec find_ #_ #_ hd l k =
  if B.is_null hd then
    None
  else
    let cell = !* hd in
    if fst cell.LL1.data = k then
      Some (snd cell.LL1.data)
    else
      find_ cell.LL1.next (List.Tot.tl l) k
#pop-options

/// A wrapper for LL2

val find (#t_k: eqtype) (#t_v: Type0) (ll: t t_k t_v) (k: t_k):
  Stack (option t_v)
    (requires fun h0 ->
      invariant h0 ll)
    (ensures fun h0 x h1 ->
      let m: map t_k t_v = v h0 ll in
      h0 == h1 /\
      x == M.sel m k)

let find #_ #_ ll k =
  find_ !*ll.LL2.ptr !*ll.LL2.v k

val add (#t_k: eqtype) (#t_v: Type0) (ll: t t_k t_v) (k: t_k) (x: t_v):
  ST unit
    (requires fun h0 ->
      invariant h0 ll)
    (ensures fun h0 _ h1 ->
      B.modifies (footprint h0 ll) h0 h1 /\
      v h1 ll == M.upd (v h0 ll) k (Some x))

#push-options "--fuel 1"
let add #_ #_ ll k x =
  LL2.push ll (k, x)
#pop-options
