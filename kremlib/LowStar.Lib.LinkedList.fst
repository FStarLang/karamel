module LowStar.Lib.LinkedList

/// This module, oftentimes referred to as LL1 in other parts of the
/// documentation, provides a low-level view over a linked list. Unless you
/// intend on modifying the structure of the linked list (e.g. removing cells)
/// or iterating over each cell, your are probably better off using LL2.
///
/// This module is intentionally not relying on a tight abstraction, to permit
/// direct-style iteration by clients.

open LowStar.BufferOps

module B = LowStar.Buffer
module HS = FStar.HyperStack
module G = FStar.Ghost
module L = FStar.List.Tot
module U32 = FStar.UInt32
module ST = FStar.HyperStack.ST

open FStar.HyperStack.ST

/// Breaking from my own recommendation here... using fuel 1 / ifuel 1 since
/// everything does recursive list reasoning.
#set-options "--__no_positivity --fuel 1 --ifuel 1"

/// Definition of the Low* type
/// ---------------------------
noeq
type t (a: Type0) =
  B.pointer_or_null (cell a)

and cell (a: Type0) = {
  next: t a;
  data: a;
}

/// Unlike the canonical style that associated a ``v`` function to any stateful
/// representation, we use a relation here. Writing a function is just
/// impossible, since we can't prove termination of ``v`` owing to the fact that
/// there may be an infinite number of cells in the heap.
///
/// Note: no need to use erased here for ``l`` since the function is already in ``GTot``.
let rec well_formed #a (h: HS.mem) (c: t a) (l: list a): GTot Type0 (decreases l) =
  B.live h c /\ (
  match l with
  | [] ->
    B.g_is_null c
  | a :: q ->
    B.length c == 1 /\ (
    let { data=data; next=next } = B.get h c 0 in
    a == data /\
    well_formed h next (G.hide q)
  ))

/// One more thing
/// --------------
///
/// The modifies clauses are given either on the footprint of the list, or on a
/// region that includes the footprint of the list (higher up the stack, e.g.
/// LL2). This is good, but does not rule out "stupid" implementations that
/// might re-allocate every single list cell when, say, doing a pop.
///
/// For advanced usages which take pointers directly to individual list cells,
/// it's important to rule out these cases. We thus define the ``cells``
/// predicate for that purpose.

let rec cells #a (h: HS.mem) (c: t a) (l: list a): Ghost (list (B.pointer (cell a)))
  (requires well_formed h c l)
  (ensures fun _ -> True)
  (decreases l)
=
  if B.g_is_null c then
    []
  else
    c :: cells h (B.deref h c).next (List.Tot.tl l)

/// This should be absolutely trivial, yet, because there's no pattern on
/// null_unique, we have to do the case analysis and the decomposition
/// ourselves. This is quite tedious, as it usually takes a while (at least it
/// did for me!) to realize that this property does not hold automatically.
///
/// I'm setting an SMTPat on this lemma because it's absolutely impossible to
/// get any work done without it.
let same_cells_same_pointer #a (h0 h1: HS.mem) (ll0 ll1: t a) (l0 l1: list a): Lemma
  (requires (
    well_formed h0 ll0 l0 /\
    well_formed h1 ll1 l1 /\
    cells h0 ll0 l0 == cells h1 ll1 l1))
  (ensures (
    ll0 == ll1))
  [ SMTPat (cells h0 ll0 l0); SMTPat (cells h1 ll1 l1) ]
=
  if B.g_is_null ll0 && B.g_is_null ll1 then begin
    B.null_unique ll0;
    B.null_unique ll1
  end else if not (B.g_is_null ll0) && not (B.g_is_null ll1) then begin
    ()
  end else
    false_elim ()

/// Classic stateful reasoning lemmas
/// ---------------------------------

val footprint: (#a: Type) -> (h: HS.mem) -> (l: t a) -> (n: list a) -> Ghost B.loc
  (requires (well_formed h l n))
  (ensures (fun refs -> True))
  (decreases n)

let rec footprint #a h l n =
  if B.g_is_null l
  then B.loc_none
  else
    let {next = next} = B.get h l 0 in
    let refs = footprint h next (G.hide (L.tl n)) in
    B.loc_union (B.loc_addr_of_buffer l) refs

/// Departing from LinkedList4 here. I prefer to bolt these into the invariant
/// rather than requiring on some wizard lemmas from LowStar.Monotonic.Buffer to
/// deduce these.
val cells_pairwise_disjoint: #a:Type -> h:HS.mem -> l:t a -> n:list a -> Ghost Type0
  (requires well_formed h l n)
  (ensures fun _ -> True)
  (decreases n)

let rec cells_pairwise_disjoint #_ h l n =
  if B.g_is_null l then
    True
  else
    let next = (B.deref h l).next in
    B.loc_disjoint (B.loc_addr_of_buffer l) (footprint h next (L.tl n)) /\
    cells_pairwise_disjoint h next (L.tl n)

val cells_live_freeable: #a:Type -> h:HS.mem -> l:t a -> n:list a -> Ghost Type0
  (requires well_formed h l n)
  (ensures fun _ -> True)
  (decreases n)

let rec cells_live_freeable #_ h l n =
  if B.g_is_null l then
    True
  else
    let next = (B.deref h l).next in
    B.live h l /\ B.freeable l /\
    cells_live_freeable h next (L.tl n)

val invariant: #a:Type -> h:HS.mem -> l: t a -> n:list a -> Ghost Type0
  (requires well_formed h l n)
  (ensures fun _ -> True)
  (decreases n)
let invariant #a h l n =
  cells_live_freeable h l n /\ cells_pairwise_disjoint h l n

/// Normally this would be automatic and writing a custom lemma for that stuff
/// would be needed only when writing an fsti, however, as stated earlier,
/// recursion makes everything more difficult and this absolutely needs to be in
/// scope otherwise the modifies-clause theory cannot deduce disjointness of
/// fresh allocations w.r.t. the footprint.
let rec invariant_loc_in_footprint (#a: Type) (h: HS.mem) (l: t a) (n: list a): Lemma
  (requires well_formed h l n)
  (ensures B.loc_in (footprint h l n) h)
  (decreases n)
  [ SMTPat (invariant h l n) ]
=
  if B.g_is_null l then
    ()
  else
    let next = (B.deref h l).next in
    invariant_loc_in_footprint h next (L.tl n)

/// Another absolutely essential lemma, for which interestingly the pattern
/// "invariant h1 l n" does not work, but well_formed does... I guess that's
/// alright.
let rec frame (#a: Type) (l: t a) (n: list a) (r: B.loc) (h0 h1: HS.mem): Lemma
  (requires (
    well_formed h0 l n /\
    invariant h0 l n /\
    B.loc_disjoint r (footprint h0 l n) /\
    B.modifies r h0 h1
  ))
  (ensures (
    well_formed h1 l n /\
    footprint h1 l n == footprint h0 l n /\
    cells h1 l n == cells h0 l n /\
    invariant h1 l n
  ))
  (decreases n)
  [ SMTPat (well_formed h1 l n); SMTPat (B.modifies r h0 h1) ]
=
  if B.g_is_null l then
    ()
  else
    frame (B.deref h0 l).next (L.tl n) r h0 h1

/// Lemmas for working with linked lists
/// ------------------------------------
///
/// Since it's a recursive data structure, a lot of the automated reasoning from
/// LowStar.Buffer doesn't work since it requires inductions. Some helpful
/// properties are therefore proved here.

let rec length_functional #a (h: HS.mem) (c: t a) (l1 l2: list a):
  Lemma
    (requires (well_formed h c l1 /\ well_formed h c l2))
    (ensures (l1 == l2))
    (decreases (G.reveal l1))
    [ SMTPat (well_formed h c l1); SMTPat (well_formed h c l2) ] =
  if B.g_is_null c
  then ()
  else
    let { next=next } = B.get h c 0 in
    length_functional h next (G.hide (L.tl l1)) (G.hide (L.tl l2))

/// These two allow conveniently switching to a low-level representation of the
/// footprint in case clients want to do some ultra-precise reasoning about
/// what's happening with the list spine. However, the fact that all
/// operations from this module specify things in terms of ``cells`` along with
/// ``same_cells_same_pointer`` should cover most common cases.
#push-options "--ifuel 1"
let rec footprint_via_cells #a (l: list (B.pointer (cell a))): GTot B.loc =
  match l with
  | c :: cs -> B.loc_addr_of_buffer c `B.loc_union` footprint_via_cells cs
  | [] -> B.loc_none
#pop-options

/// TODO: move to LL2
#push-options "--fuel 1 --ifuel 1"
let rec footprint_via_cells_is_footprint #a (h: HS.mem) (ll: t a) (l: list a): Lemma
  (requires well_formed h ll l)
  (ensures
    footprint h ll l == footprint_via_cells (cells h ll l))
  (decreases l)
=
  if B.g_is_null ll then
    ()
  else
    footprint_via_cells_is_footprint h (B.deref h ll).next (List.Tot.tl l)
#pop-options

/// The footprint is based on loc_addr_of_buffer so that we can write a free
/// operation that operates on the footprint. However, this invalidates most of
/// the helper lemmas for disjointness that were present in the previous
/// iteration of this module, named LinkedList4.fst.

/// Stateful operations
/// -------------------
///
/// One thing to note: we pass the region `r` explicitly, which is certainly not
/// very convenient, but that's alright, another layer of abstraction will take
/// care of adding existentials and extra machinery to make this more pleasant
/// to use.
///
/// All of the operations below are low-level (in the sense that they rely on
/// the predicate). I expect clients to use exclusively the variants of these
/// functions present in LL2.

val push: (#a: Type) -> (r: HS.rid) -> (n: G.erased (list a)) -> (pl: B.pointer (t a)) -> (x: a) ->
  ST unit
    (requires (fun h ->
      let l = B.deref h pl in
      B.live h pl /\
      well_formed h l n /\
      invariant h l n /\
      ST.is_eternal_region r /\
      B.(loc_includes (loc_region_only true r) (footprint h l n)) /\
      B.(loc_disjoint (loc_buffer pl) (loc_region_only true r))
    ))
    (ensures (fun h0 _ h1 ->
      let n' = G.hide (x :: G.reveal n) in
      let l = B.deref h1 pl in
      // Style note: I don't repeat ``B.live pl`` in the post-condition since
      // ``B.modifies (loc_buffer pl) h0 h1`` implies that ``B.live h1 pl``.
      B.modifies (B.loc_buffer pl) h0 h1 /\
      well_formed h1 l n' /\
      invariant h1 l n' /\
      B.(loc_includes (loc_region_only true r) (footprint h1 l n') /\
      Cons? (cells h1 l n') /\ List.Tot.tail (cells h1 l n') == cells h0 (B.deref h0 pl) n /\
      B.fresh_loc (B.loc_addr_of_buffer (List.Tot.hd (cells h1 l n'))) h0 h1)
    ))

let push #a r n pl x =
  (**) let h0 = ST.get () in
  let l = !* pl in
  let c = { data = x; next = l } in

  let pc: B.pointer (cell a) = B.malloc r c 1ul in
  (**) let h1 = ST.get () in
  (**) B.(modifies_only_not_unused_in loc_none h0 h1);
  (**) assert B.(loc_disjoint (loc_buffer pc) (footprint h0 l n));

  pl *= pc;
  (**) let h2 = ST.get () in
  (**) let n' = G.hide (x :: G.reveal n) in
  (**) B.(modifies_trans loc_none h0 h1 (loc_buffer pl) h2);
  (**) assert (well_formed h2 (B.deref h2 pl) n');
  (**) assert (invariant h2 (B.deref h2 pl) n');
  (**) assert ((B.deref h2 (B.deref h2 pl)).next == l);

  ()

val pop: (#a: Type) -> (r: HS.rid) -> (n: G.erased (list a)) -> (pl: B.pointer (t a)) ->
  ST a
    (requires (fun h ->
      let l = B.deref h pl in
      B.live h pl /\
      well_formed h l n /\
      invariant h l n /\
      ST.is_eternal_region r /\
      B.(loc_includes (loc_region_only true r) (footprint h l n)) /\
      B.loc_disjoint (B.loc_buffer pl) (footprint h l n) /\
      Cons? n
    ))
    (ensures (fun h0 x h1 ->
      let l = B.deref h1 pl in
      let n' = L.tl n in
      x == L.hd n /\
      // Introducing a super precise modifies clause (e.g. loc_addr_of_buffer
      // (B.deref h0 pl)) here is not useful and prevents trigger-based
      // reasoning, while also requiring clients to unroll footprint. There's a
      // tension here between revealing that ``pop`` does nothing stupid (e.g.
      // re-allocating all the list cells) and providing an abstract enough
      // predicate to work with.
      B.(modifies (loc_buffer pl `loc_union` footprint h0 (B.deref h0 pl) n) h0 h1) /\
      well_formed h1 l n' /\
      invariant h1 l n' /\
      B.(loc_includes (loc_region_only true r) (footprint h1 l n')) /\
      List.Tot.tail (cells h0 (B.deref h0 pl) n) == cells h1 l n'))

let pop #a r n pl =
  let l = !* pl in
  let r = (!*l).data in
  let next = (!*l).next in
  (**) let h1 = ST.get () in
  (**) assert (cells h1 l n == l :: cells h1 next (List.Tot.tl n));
  (**) assert B.(loc_disjoint (loc_buffer pl) (footprint h1 l n));
  (**) assert B.(loc_disjoint (loc_buffer pl) (footprint h1 next (List.Tot.tl n)));

  pl *= next;
  B.free l;
  r

val free_: (#a: Type) -> (#n: G.erased (list a)) -> (l: t a) ->
  ST unit
    (requires (fun h ->
      well_formed h l n /\
      invariant h l n
    ))
    (ensures (fun h0 _ h1 ->
      B.(modifies (footprint h0 l n) h0 h1)))

let rec free_ #a #n l =
  if B.is_null l then
    ()
  else begin
    let tl: G.erased (list a) = G.hide (L.tl (G.reveal n)) in
    free_ #_ #tl (!*l).next;
    B.free l
  end

val free: (#a: Type) -> (#n: G.erased (list a)) -> (pl: B.pointer (t a)) ->
  ST unit
    (requires (fun h ->
      let l = B.deref h pl in
      B.live h pl /\
      well_formed h l n /\
      invariant h l n /\
      B.loc_disjoint (B.loc_buffer pl) (footprint h l n)
    ))
    (ensures (fun h0 _ h1 ->
      let l = B.deref h1 pl in
      well_formed h1 l [] /\
      invariant h1 l [] /\
      footprint h1 l [] == B.loc_none /\
      cells h1 l [] == [] /\
      B.(modifies (footprint h0 (B.deref h0 pl) n `loc_union` loc_buffer pl) h0 h1)))

let free #a #n pl =
  free_ #_ #n !*pl;
  pl *= B.null

val length (#a: Type) (gn: G.erased (list a)) (l: t a): Stack UInt32.t
  (requires (fun h -> well_formed h l gn))
  (ensures (fun h0 n h1 ->
    h0 == h1 /\
    U32.v n = L.length (G.reveal gn)
  ))

let rec length #a gn l =
  if B.is_null l then
    0ul
  else
    let open U32 in
    let c = !* l in
    let next = c.next in
    let n = length (G.hide (L.tail (G.reveal gn))) next in
    if n = 0xfffffffful then begin
      LowStar.Failure.failwith "Integer overflow in LowStar.LinkedList.length"
    end else
      n +^ 1ul

val test: unit -> ST (Int32.t) (fun _ -> true) (fun _ _ _ -> true)

let test () =
  let l: B.pointer_or_null (t Int32.t) = B.malloc HS.root B.null 1ul in
  let l_region = new_region HS.root in
  push #Int32.t l_region (G.hide []) l 1l;
  push #Int32.t l_region (G.hide [1l]) l 0l;
  let r = pop #Int32.t l_region (G.hide [0l; 1l]) l in
  TestLib.checku32 (length (G.hide [1l]) !*l) 1ul;
  r
