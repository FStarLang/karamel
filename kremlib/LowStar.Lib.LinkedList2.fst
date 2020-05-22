module LowStar.Lib.LinkedList2

open LowStar.BufferOps

module B = LowStar.Buffer
module HS = FStar.HyperStack
module G = FStar.Ghost
module L = FStar.List.Tot
module U32 = FStar.UInt32
module ST = FStar.HyperStack.ST

module LL = LowStar.Lib.LinkedList

open FStar.HyperStack.ST

#set-options "--fuel 0 --ifuel 0"

noeq
type t a = {
  ptr: B.pointer (LL.t a);
  // Relies on an upcoming pointer-to-unit elimination phase in KreMLin
  v: B.pointer (G.erased (list a));
  r: HS.rid;
  spine_rid: HS.rid;
  ptr_rid: HS.rid;
}

val invariant: #a:Type -> h:HS.mem -> ll:t a -> Type0
let invariant #a h ll =
  let head = B.deref h ll.ptr in
  let v = B.deref h ll.v in
  B.live h ll.ptr /\
  B.freeable ll.ptr /\
  B.live h ll.v /\
  B.freeable ll.v /\
  LL.well_formed h head v /\
  LL.invariant h head v /\

  ST.is_eternal_region ll.r /\
  ST.is_eternal_region ll.spine_rid /\
  ST.is_eternal_region ll.ptr_rid /\
  B.(loc_includes (loc_region_only true ll.ptr_rid) (loc_addr_of_buffer ll.ptr `loc_union` loc_addr_of_buffer ll.v)) /\
  B.(loc_includes (loc_region_only true ll.spine_rid) (LL.footprint h head v)) /\
  B.(loc_disjoint (loc_addr_of_buffer ll.ptr) (loc_addr_of_buffer ll.v)) /\
  B.(loc_disjoint (loc_region_only true ll.ptr_rid) (loc_region_only true ll.spine_rid)) /\

  HS.extends ll.ptr_rid ll.r /\
  HS.extends ll.spine_rid ll.r /\
  HS.parent ll.ptr_rid == ll.r /\
  HS.parent ll.spine_rid == ll.r

val footprint: #a:Type -> h:HS.mem -> ll: t a -> Ghost B.loc
  (requires invariant h ll)
  (ensures fun _ -> True)
let footprint #a h ll =
  let head = B.deref h ll.ptr in
  let v = B.deref h ll.v in
  B.(loc_addr_of_buffer ll.ptr `loc_union` loc_addr_of_buffer ll.v `loc_union` LL.footprint h head v)

val v: #a:Type -> h:HS.mem -> ll: t a -> GTot (list a)
let v #_ h ll =
  B.deref h ll.v

/// This is a most useful lemma for clients: all the bookkeeping of this linked
/// list, including spine, is subsumed in region r. Clients will typically
/// allocate a fresh region for r and will maintain the invariant that their own
/// data structures are disjoint from ``r``, hence getting easy framing at any
/// time.
let footprint_in_r #a (h: HS.mem) (ll: t a): Lemma
  (requires invariant h ll)
  (ensures B.(loc_includes (loc_all_regions_from true ll.r) (footprint h ll)))
=
  assert B.(loc_includes (loc_region_only true ll.spine_rid) (LL.footprint h (B.deref h ll.ptr) (v h ll)));
  assert B.(loc_includes (loc_all_regions_from true ll.r) (loc_region_only true ll.spine_rid))

val frame (#a: Type) (ll: t a) (l: B.loc) (h0 h1: HS.mem): Lemma
  (requires
    invariant h0 ll /\
    B.loc_disjoint l (footprint h0 ll) /\
    B.modifies l h0 h1)
  (ensures
    invariant h1 ll /\
    footprint h1 ll == footprint h0 ll)
let frame #_ _ _ _ _ =
  ()

val create_in: #a:Type -> r:HS.rid -> ST (t a)
  (requires fun h0 ->
    ST.is_eternal_region r)
  (ensures fun h0 ll h1 ->
    invariant h1 ll /\
    B.(modifies loc_none h0 h1) /\
    B.fresh_loc (footprint h1 ll) h0 h1 /\
    v h1 ll == [])

#push-options "--fuel 1"
let create_in #a r =
  let ptr_rid = ST.new_region r in
  let spine_rid = ST.new_region r in
  let ptr = B.malloc ptr_rid (B.null <: LL.t a) 1ul in
  let v = B.malloc ptr_rid (G.hide ([] <: list a)) 1ul in
  { ptr; v; r; ptr_rid; spine_rid }
#pop-options

val push: #a:Type -> ll: t a -> x: a -> ST unit
  (requires fun h0 ->
    invariant h0 ll)
  (ensures fun h0 _ h1 ->
    invariant h1 ll /\
    B.(modifies (loc_buffer ll.ptr `loc_union` loc_buffer ll.v) h0 h1) /\
    B.(loc_includes (loc_all_regions_from true ll.r) (footprint h1 ll)) /\
    v h1 ll == x :: v h0 ll)

let push #a ll x =
  LL.push ll.spine_rid (!* ll.v) ll.ptr x;
  let v = !* ll.v in
  ll.v *= G.hide (x :: v);
  let h2 = ST.get () in
  assert (LL.well_formed h2 (B.deref h2 ll.ptr) (x :: v))
