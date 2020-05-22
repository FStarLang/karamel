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

// Modulo the upcoming KreMLin optimization, this type will extract just like
// ``B.pointer (LL.t a)`` would, with no indirection due to the record.
noeq
type t a = {
  ptr: B.pointer (LL.t a);
  // Relies on an upcoming pointer-to-unit elimination phase in KreMLin
  v: B.pointer (G.erased (list a));
  // For separation; all erased.
  r: HS.rid;
  spine_rid: HS.rid;
  ptr_v_rid: HS.rid;
}

val invariant: #a:Type -> h:HS.mem -> ll:t a -> Type0
let invariant #a h ll =
  let head = B.deref h ll.ptr in
  let v = B.deref h ll.v in
  // This is where we switch from a predicate (cumbersome for clients, requires
  // materializing the list at any time) to a ``v`` function which makes
  // specifications much easier. Any time the invariant holds, the pointer ``v``
  // holds a computationally-irrelevant representation of the list that in turns
  // allows us to under-the-hood state the various predicates from LL that
  // require exhibiting a list.
  B.live h ll.ptr /\
  B.freeable ll.ptr /\
  B.live h ll.v /\
  B.freeable ll.v /\
  LL.well_formed h head v /\
  LL.invariant h head v /\

  // We use regions for separation only, not for any footprint reasoning:
  // - ptr_v_rid is a sub-region of r and contains ptr and v, disjoint from each other
  // - spine_rid is a sub-region of r, disjoint from ptr_v_rid, and contains the LL.footprint
  ST.is_eternal_region ll.r /\
  ST.is_eternal_region ll.spine_rid /\
  ST.is_eternal_region ll.ptr_v_rid /\
  B.(loc_includes (loc_region_only true ll.ptr_v_rid) (loc_addr_of_buffer ll.ptr `loc_union` loc_addr_of_buffer ll.v)) /\
  B.(loc_includes (loc_region_only true ll.spine_rid) (LL.footprint h head v)) /\
  B.(loc_disjoint (loc_addr_of_buffer ll.ptr) (loc_addr_of_buffer ll.v)) /\
  B.(loc_disjoint (loc_region_only true ll.ptr_v_rid) (loc_region_only true ll.spine_rid)) /\

  // These are not redundant, and are important for showing that the footprint
  // is contained in ``r`` at any time, so long as the invariant holds.
  HS.extends ll.ptr_v_rid ll.r /\
  HS.extends ll.spine_rid ll.r /\
  HS.parent ll.ptr_v_rid == ll.r /\
  HS.parent ll.spine_rid == ll.r

val footprint: #a:Type -> h:HS.mem -> ll: t a -> Ghost B.loc
  (requires invariant h ll)
  (ensures fun _ -> True)
let footprint #a h ll =
  let head = B.deref h ll.ptr in
  let v = B.deref h ll.v in
  B.(loc_addr_of_buffer ll.ptr `loc_union` loc_addr_of_buffer ll.v `loc_union` LL.footprint h head v)

/// There! Much easier reasoning for clients.
val v: #a:Type -> h:HS.mem -> ll: t a -> GTot (list a)
let v #_ h ll =
  B.deref h ll.v

/// This is a most useful lemma for clients: all the bookkeeping of this linked
/// list, including spine, is subsumed in region r, at any time.
///
/// This allows clients to allocate a new region for ``r``, maintain the
/// invariant that ``r`` is disjoint from their own data structures, and get
/// easy separation and framing for their own data this way.
///
/// Note that we don't generally have to state such lemmas, since in many cases,
/// footprints are static and do not grow dynamically.
let footprint_in_r #a (h: HS.mem) (ll: t a): Lemma
  (requires invariant h ll)
  (ensures B.(loc_includes (loc_all_regions_from true ll.r) (footprint h ll)))
=
  assert B.(loc_includes (loc_region_only true ll.spine_rid) (LL.footprint h (B.deref h ll.ptr) (v h ll)));
  assert B.(loc_includes (loc_all_regions_from true ll.r) (loc_region_only true ll.spine_rid))

/// This lemma is perhaps overly precise, but for clients, as long as they know
/// they are disjoint from ``r``, they can conclude they are disjoint from the
/// footprint via the lemma above.
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
  let ptr_v_rid = ST.new_region r in
  let spine_rid = ST.new_region r in
  let ptr = B.malloc ptr_v_rid (B.null <: LL.t a) 1ul in
  let v = B.malloc ptr_v_rid (G.hide ([] <: list a)) 1ul in
  { ptr; v; r; ptr_v_rid; spine_rid }
#pop-options

val push: #a:Type -> ll: t a -> x: a -> ST unit
  (requires fun h0 ->
    invariant h0 ll)
  (ensures fun h0 _ h1 ->
    invariant h1 ll /\
    B.(modifies (loc_buffer ll.ptr `loc_union` loc_buffer ll.v) h0 h1) /\
    v h1 ll == x :: v h0 ll)

let push #a ll x =
  LL.push ll.spine_rid (!* ll.v) ll.ptr x;
  let v = !* ll.v in
  ll.v *= G.hide (x :: v)

val pop: #a:Type -> ll: t a -> ST a
  (requires fun h0 ->
    invariant h0 ll /\
    Cons? (v h0 ll))
  (ensures fun h0 x h1 ->
    let hd :: tl = v h0 ll in
    invariant h1 ll /\
    B.(modifies (loc_buffer ll.ptr `loc_union` loc_buffer ll.v) h0 h1) /\
    v h1 ll == tl /\
    x == hd)

let pop #a ll =
  let r = LL.pop ll.spine_rid (!* ll.v) ll.ptr in
  let v = !* ll.v in
  ll.v *= G.hide (List.Tot.tl v);
  r

val maybe_pop: #a:Type -> ll: t a -> ST (option a)
  (requires fun h0 ->
    invariant h0 ll)
  (ensures fun h0 x h1 ->
    invariant h1 ll /\
    B.(modifies (loc_buffer ll.ptr `loc_union` loc_buffer ll.v) h0 h1) /\ (
    match x with
    | Some x ->
        Cons? (v h0 ll) /\ (
        let hd :: tl = v h0 ll in
        v h1 ll == tl /\
        x == hd)
    | None ->
        Nil? (v h0 ll)))

#push-options "--fuel 1 --ifuel 1"
let maybe_pop #a ll =
  if not (B.is_null (!* ll.ptr)) then
    let v = !* ll.v in
    let r = LL.pop ll.spine_rid (!* ll.v) ll.ptr in
    ll.v *= G.hide (List.Tot.tl v);
    Some r
  else
    None
#pop-options

val clear: #a:Type -> ll: t a -> ST unit
  (requires fun h0 ->
    invariant h0 ll)
  (ensures fun h0 _ h1 ->
    invariant h1 ll /\
    B.(modifies (loc_buffer ll.ptr `loc_union` loc_buffer ll.v `loc_union` loc_region_only true ll.spine_rid) h0 h1) /\
    v h1 ll == [])

let clear #a ll =
  let v = !* ll.v in
  LL.free #_ #v ll.ptr;
  ll.v *= G.hide []

val free: #a:Type -> ll: t a -> ST unit
  (requires fun h0 ->
    invariant h0 ll)
  (ensures fun h0 _ h1 ->
    B.(modifies (footprint h0 ll) h0 h1))

let free #_ ll =
  let v = !* ll.v in
  LL.free #_ #v ll.ptr;
  B.free ll.ptr;
  B.free ll.v
