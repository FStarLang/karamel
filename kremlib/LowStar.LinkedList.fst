module LowStar.LinkedList

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
let rec well_formed #a (h: HS.mem) (c: t a) (l: list a): GTot Type0 (decreases (G.reveal l)) =
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

/// The footprint is based on loc_addr_of_buffer so that we can write a free
/// operation that operates on the footprint. However, this invalidates most of
/// the helper lemmas for disjointness that were present in the previous
/// iteration of this module, named LinkedList4.fst.

/// Stateful operations
/// -------------------

val push: (#a: Type) -> (#n: G.erased (list a)) -> (pl: B.pointer (t a)) -> (x: a) ->
  ST unit
    (requires (fun h ->
      let l = B.deref h pl in
      B.live h pl /\
      well_formed h l n /\
      invariant h l n /\
      B.loc_disjoint (B.loc_buffer pl) (footprint h l n)
    ))
    (ensures (fun h0 _ h1 ->
      let n' = G.hide (x :: G.reveal n) in
      let l = B.deref h1 pl in
      // Liveness follows for pl from modifies loc_buffer (not loc_addr_of_buffer)
      B.modifies (B.loc_buffer pl) h0 h1 /\
      well_formed h1 l n' /\
      invariant h1 l n' /\ (
      forall (l': B.loc). {:pattern B.(loc_disjoint l' (footprint h0 (deref h0 pl) n)) }
        B.(loc_in l' h0 /\ loc_disjoint l' (footprint h0 (deref h0 pl) n)) ==>
        B.loc_disjoint l' (footprint h1 l n')
    )))

let push #a #n pl x =
  (**) let h0 = ST.get () in
  let l = !* pl in
  let c = { data = x; next = l } in

  let pc: B.pointer (cell a) = B.malloc HS.root c 1ul in
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

val pop: (#a: Type) -> (#n: G.erased (list a)) -> (pl: B.pointer (t a)) ->
  ST a
    (requires (fun h ->
      let l = B.deref h pl in
      B.live h pl /\
      well_formed h l n /\
      invariant h l n /\
      B.loc_disjoint (B.loc_buffer pl) (footprint h l n) /\
      Cons? n
    ))
    (ensures (fun h0 _ h1 ->
      let l = B.deref h1 pl in
      let n' = L.tl n in
      // Liveness follows for pl from modifies loc_buffer (not loc_addr_of_buffer)
      B.modifies (B.loc_buffer pl) h0 h1 /\
      well_formed h1 l n' /\
      invariant h1 l n' /\ (
      forall (l': B.loc). {:pattern B.(loc_disjoint l' (footprint h0 (deref h0 pl) n)) }
        B.(loc_in l' h0 /\ loc_disjoint l' (footprint h0 (deref h0 pl) n)) ==>
        B.loc_disjoint l' (footprint h1 l n')
    )))

let pop #a #n pl =
  let l = !* pl in
  let r = (!*l).data in
  pl *= (!*l).next;
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

val main: unit -> ST (Int32.t) (fun _ -> true) (fun _ _ _ -> true)

let main () =
  let l: B.pointer_or_null (t Int32.t) = B.malloc HS.root B.null 1ul in
  push #Int32.t #(G.hide []) l 1l;
  push #Int32.t #(G.hide [1l]) l 0l;
  let r = pop #Int32.t #(G.hide [0l; 1l]) l in
  TestLib.checku32 (length (G.hide [1l]) !*l) 1ul;
  r
