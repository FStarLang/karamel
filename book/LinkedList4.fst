/// Example: linked list
/// ====================

module LinkedList4
open LowStar.BufferOps

module B = LowStar.Buffer
module HS = FStar.HyperStack
module G = FStar.Ghost
module L = FStar.List.Tot
module U32 = FStar.UInt32
module MO = LowStar.Modifies

open FStar.HyperStack.ST

#set-options "--__no_positivity --use_two_phase_tc true"

/// We revisit the classic example of lists, but in a low-level
/// setting, using linked lists. This second version uses
/// `B.pointer_or_null`, the type of buffers of length 1 or 0.
noeq
type t (a: Type0) =
  B.pointer_or_null (cell a)

and cell (a: Type0) = {
  next: t a;
  data: a;
}

/// We enrich lists with a predicate that captures their length.  This
/// predicate will be needed for any traversal of the list, in order
/// to show termination.  This predicate also encodes the fact that
/// all cells of the list are live at the same time.  The absence of
/// cycles does not suffice to guarantee termination, as the number of
/// buffers in the heap is potentially infinite;
let rec well_formed #a (h: HS.mem) (c: t a) (l: G.erased (list a))
: GTot Type0 (decreases (G.reveal l))
= B.live h c /\ (
  match G.reveal l with
  | [] ->
    B.g_is_null c
  | a :: q ->
    B.length c == 1 /\ (
    let { data=data; next=next } = B.get h c 0 in
    a == data /\
    well_formed h next (G.hide q)
  ))

/// Note: all the ghost predicates and functions operate on a length of type
/// nat; the Ghost effect guarantees that the length can only be used at
/// run-time. Functions called at run-time will, conversely, use a length of
/// type `erased nat`, which states that the length is
/// computationally-irrelevant and can be safely removed from the resulting C
/// code via a combination of F* + KreMLin erasure.

let rec length_functional #a (h: HS.mem) (c: t a) (l1 l2: G.erased (list a)):
  Lemma
    (requires (well_formed h c l1 /\ well_formed h c l2))
    (ensures (l1 == l2))
    (decreases (G.reveal l1))
    [ SMTPat (well_formed h c l1); SMTPat (well_formed h c l2) ] =
  if B.g_is_null c
  then ()
  else
    let { next=next } = B.get h c 0 in
    length_functional h next (G.hide (L.tl (G.reveal l1))) (G.hide (L.tl (G.reveal l2)))

/// As we start proving some degree of functional correctness, we will have to
/// reason about non-interference, and state that some operations do not modify
/// the footprint of a given list.
#set-options "--max_ifuel 1 --max_fuel 2"
val footprint: (#a: Type) -> (h: HS.mem) -> (l: t a) -> (n: G.erased (list a)) -> Ghost MO.loc
  (requires (well_formed h l n))
  (ensures (fun refs -> True))
  (decreases (G.reveal n))

let rec footprint #a h l n =
  if B.g_is_null l
  then MO.loc_none
  else
    let {next = next} = B.get h l 0 in
    let refs = footprint h next (G.hide (L.tl (G.reveal n))) in
    MO.loc_union (MO.loc_buffer l) refs
#reset-options

let rec modifies_disjoint_footprint
  (#a: Type)
  (h: HS.mem)
  (l: t a)
  (n: G.erased (list a))
  (r: MO.loc)
  (h' : HS.mem)
: Lemma
  (requires (
    well_formed h l n /\
    MO.loc_disjoint r (footprint h l n) /\
    MO.modifies r h h'
  ))
  (ensures (
    well_formed h' l n /\
    footprint h' l n == footprint h l n
  ))
  (decreases (G.reveal n))
= if B.g_is_null l
  then ()
  else begin
    let {next = l'} = B.get h l 0 in
    modifies_disjoint_footprint h l' (G.hide (L.tl (G.reveal n))) r h'
  end

let rec well_formed_distinct_lengths_disjoint
  #a
  (c1: B.pointer (cell a))
  (c2: B.pointer (cell a))
  (n1: G.erased (list a))
  (n2: G.erased (list a))
  (h: HS.mem)
: Lemma
  (requires (
    well_formed h c1 n1 /\
    well_formed h c2 n2 /\
    L.length (G.reveal n1) <> L.length (G.reveal n2)
  ))
  (ensures (
    B.disjoint c1 c2
  ))
  (decreases (L.length (G.reveal n1) + L.length (G.reveal n2)))
= let {next = next1} = B.get h c1 0 in
  let {next = next2} = B.get h c2 0 in
  let f () : Lemma (next1 =!= next2) =
    if B.g_is_null next1 || B.g_is_null next2
    then ()
    else
      well_formed_distinct_lengths_disjoint next1 next2 (G.hide (L.tl (G.reveal n1))) (G.hide (L.tl (G.reveal n2))) h
  in
  f ();
  B.pointer_distinct_sel_disjoint c1 c2 h

let rec well_formed_gt_lengths_disjoint_from_list
  #a
  (h: HS.mem)
  (c1: B.pointer_or_null (cell a))
  (c2: B.pointer_or_null (cell a))
  (n1: G.erased (list a))
  (n2: G.erased (list a))
: Lemma
  (requires (well_formed h c1 n1 /\ well_formed h c2 n2 /\ L.length (G.reveal n1) > L.length (G.reveal n2)))
  (ensures (MO.loc_disjoint (MO.loc_buffer c1) (footprint h c2 n2)))
  (decreases (G.reveal n2))
= match G.reveal n2 with
  | [] -> ()
  | _ ->
    well_formed_distinct_lengths_disjoint c1 c2 n1 n2 h;
    well_formed_gt_lengths_disjoint_from_list h c1 (B.get h c2 0).next n1 (G.hide (L.tl (G.reveal n2)))

let well_formed_head_tail_disjoint
  (#a: Type)
  (h: HS.mem)
  (c: B.pointer (cell a))
  (n: G.erased (list a))
: Lemma
  (requires (well_formed h c n))
  (ensures (
    MO.loc_disjoint (MO.loc_buffer c) (footprint h (B.get h c 0).next (G.hide (L.tl (G.reveal n))))
  ))
= well_formed_gt_lengths_disjoint_from_list h c (B.get h c 0).next n (G.hide (L.tl (G.reveal n)))

let rec unused_in_well_formed_disjoint_from_list
  #a #b
  (h: HS.mem)
  (r: B.buffer a)
  (l: B.pointer_or_null (cell b))
  (n: G.erased (list b))
: Lemma
  (requires (r `B.unused_in` h /\ well_formed h l n))
  (ensures (MO.loc_disjoint (MO.loc_buffer r) (footprint h l n)))
  (decreases (G.reveal n))
= match G.reveal n with
  | [] -> ()
  | _ -> unused_in_well_formed_disjoint_from_list h r (B.get h l 0).next (G.hide (L.tl (G.reveal n)))

/// Finally, the pop operation. Here we use the classic representation
/// using null pointers, which requires the client to pass a pointer
/// to a pointer, which is then filled with the address of the next
/// cell, or null if this was the last element in the list.

/// The code is straightforward and crucially relies on the call to the lemma
/// above. Note that at this stage we do not prove full functional correctness
/// of our implementation. Rather, we just state that the lengths is as
/// expected.

/// This version uses an erased integer n; we have to work a little bit to
/// hide/reveal the computationally-irrelevant length.
val pop: (#a: Type) -> (#n: G.erased (list a)) -> (pl: B.pointer (t a)) ->
  Stack a
  (requires (fun h ->
    let l = B.get h pl 0 in
    B.live h pl /\
    well_formed h l n /\
    MO.loc_disjoint (MO.loc_buffer pl) (footprint h l n) /\
    Cons? (G.reveal n)
  ))
  (ensures (fun h0 v h1 ->
    let l = B.get h1 pl 0 in
    let n' = G.hide (L.tl (G.reveal n)) in
    B.live h1 pl /\
    MO.modifies (MO.loc_buffer pl) h0 h1 /\
    well_formed h1 l n' /\
    MO.loc_disjoint (MO.loc_buffer pl) (footprint h1 l n')
  ))

let pop #a #n pl =
  let l = !* pl in
  let lcell = !* l in
  let h0 = get () in
  pl *= lcell.next;
  let h1 = get () in
  well_formed_head_tail_disjoint h0 l n;
  modifies_disjoint_footprint h0 l n (MO.loc_buffer pl) h1;
  lcell.data

val push: (#a: Type) -> (#n: G.erased (list a)) -> (pl: B.pointer (t a)) -> (x: a) ->
  ST unit
    (requires (fun h ->
      let l = B.get h pl 0 in
      B.live h pl /\
      well_formed h l n /\
      MO.loc_disjoint (MO.loc_buffer pl) (footprint h l n)
    ))
    (ensures (fun h0 _ h1 ->
      let n' = G.hide (x :: G.reveal n) in
      let l = B.get h1 pl 0 in
      MO.modifies (MO.loc_buffer pl) h0 h1 /\
      B.live h1 pl /\
      well_formed h1 l n' /\
      MO.loc_disjoint (MO.loc_buffer pl) (footprint h1 l n')
    ))

let push #a #n pl x =
  let h0 = get () in
  let l = !* pl in
  let c = {
    data = x;
    next = l;
  }
  in
  let pc: B.pointer (cell a) = B.malloc HS.root c 1ul in
  unused_in_well_formed_disjoint_from_list h0 pc l n;
  let h1 = get () in
  modifies_disjoint_footprint h0 l n (MO.loc_buffer pc) h1;
  pl *= pc;
  let h2 = get () in
  modifies_disjoint_footprint h1 l n (MO.loc_buffer pl) h2

/// Connecting our predicate `well_formed` to the regular length function.
/// Note that this function takes a list whose length is unknown statically,
/// because of the existential quantification.
val length (#a: Type) (gn: G.erased (list a)) (l: t a): Stack UInt32.t
  (requires (fun h -> well_formed h l gn))
  (ensures (fun h0 n h1 ->
    h0 == h1 /\
    U32.v n = L.length (G.reveal gn)
  ))

/// Note that we could have as easily returned an option, but sometimes fatal
/// errors are just easier to handle for client code. The `C.String` module
/// provides facilities for dealing with constant C string literals. It reveals
/// that they are zero-terminated and allows looping over them if one wants to,
/// say, copy an immutable constant string into a mutable buffer.
let rec length #a gn l =
  if B.is_null l
  then 0ul
  else
    let open U32 in
    let c = !* l in
    let next = c.next in
    let n = length (G.hide (L.tail (G.reveal gn))) next in
    if n = 0xfffffffful then begin
      C.String.(print !$"Integer overflow while computing length");
      C.exit 255l;
      0ul // dummy return value, this point is unreachable
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
