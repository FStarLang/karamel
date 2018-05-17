module LinkedList1

module B = FStar.Buffer
module HS = FStar.HyperStack
module G = FStar.Ghost
module L = FStar.List.Tot
module U32 = FStar.UInt32

open FStar.HyperStack.ST

#set-options "--__no_positivity --use_two_phase_tc true"

/// We revisit the classic example of lists, but in a low-level setting, using
/// linked lists. This first version uses `ref`, the type of references that are
/// always live. However, we don't cheat, and don't recall liveness "for free".
noeq
type t (a: Type0) =
  ref (cell a)

and cell (a: Type0) =
  | Nil: cell a
  | Cons:
      next: t a ->
      data: a ->
      cell a

/// Since linked lists go through a reference for indirection
/// purposes, we enrich lists with a predicate that captures their
/// length.  This predicate also encodes the fact that all cells of
/// the list are live at the same time.  This predicate will be needed
/// for any traversal of the list, in order to show termination.  The
/// absence of cycles does not suffice to guarantee termination, as
/// the number of references in the heap is potentially infinite;
let rec well_formed #a (h: HS.mem) (c: t a) (l: nat):
  GTot Type0 (decreases l)
= HS.contains h c /\ (
    match HS.sel h c with
    | Nil -> l = 0
    | Cons next _ ->
      if l = 0 then
        false
      else
        well_formed h next (l - 1)
  )

/// Note: all the ghost predicates and functions operate on a length of type
/// nat; the Ghost effect guarantees that the length can only be used at
/// run-time. Functions called at run-time will, conversely, use a length of
/// type `erased nat`, which states that the length is
/// computationally-irrelevant and can be safely removed from the resulting C
/// code via a combination of F* + KreMLin erasure.

/// When traversing a list `l` such that `well_formed h l n`, it is often
/// the case that we recursively visit the Cons cell, passing `n - 1` for the
/// recursive call. This lemma ensures that Z3 can show that `n - 1` has type
/// `nat`.
let cons_nonzero_length #a (h: HS.mem) (c: ref (cell a)) (l: nat):
  Lemma
    (requires (well_formed h c l /\ Cons? (HS.sel h c)))
    (ensures (l <> 0))
    [ SMTPat (well_formed h c l); SMTPat (Cons? (HS.sel h c)) ] =
    ()

let rec length_functional #a (h: HS.mem) (c: ref (cell a)) (l1 l2: nat):
  Lemma
    (requires (well_formed h c l1 /\ well_formed h c l2))
    (ensures (l1 = l2))
    (decreases l1)
    [ SMTPat (well_formed h c l1); SMTPat (well_formed h c l2) ] =
  match HS.sel h c with
  | Nil -> ()
  | Cons next _ ->
      // Without `cons_nonzero_length`, we would need assert (l1 <> 0)
      length_functional h next (l1 - 1) (l2 - 1)

/// This form will rarely turn out to be useful, except perhaps for user code.
/// Indeed, we most often want to tie the length of the list in the final state
/// with its length in the original state.
let live #a (h: HS.mem) (l: t a) =
  exists n. well_formed #a h l n

let live_nil #a (h: HS.mem) (l: ref (cell a)) : Lemma
  (requires (HS.contains h l /\ Nil? (HS.sel h l)))
  (ensures (live h l))
= assert (well_formed h l 0)

let live_cons #a (h: HS.mem) (l: ref (cell a)) : Lemma
  (requires (HS.contains h l /\ Cons? (HS.sel h l) /\ live h (Cons?.next (HS.sel h l))))
  (ensures (live h l))
= assert (forall n . well_formed h (Cons?.next (HS.sel h l)) n ==> well_formed h l (n + 1))

/// TODO: move to FStar.Monotonic.HyperStack
/// Disjointness of two references

let disjoint (#a1 #a2: Type) (r1: ref a1) (r2: ref a2) : GTot bool =
  HS.frameOf r1 <> HS.frameOf r2 || HS.as_addr r1 <> HS.as_addr r2

/// Disjointness of a reference wrt. a list of references of the same type

let rec disjoint_from_list (#a #b: Type) (r: ref a) (l: list (ref b)) : GTot bool =
  match l with
  | [] -> true
  | r' :: q -> disjoint r r' && disjoint_from_list r q

/// As we start proving some degree of functional correctness, we will have to
/// reason about non-interference, and state that some operations do not modify
/// the footprint of a given list.
#set-options "--max_ifuel 1 --max_fuel 2"
val footprint: (#a: Type) -> (h: HS.mem) -> (l: t a) -> (n: nat) -> Ghost (list (ref (cell a)))
  (requires (well_formed h l n))
  (ensures (fun refs ->
    let n_refs = L.length refs in
    n_refs == n + 1 /\
    (forall (i: nat). {:pattern (L.index refs i)}
      i <= n ==> well_formed h (L.index refs i) (n - i))))
  (decreases n)

let rec footprint #a h l n =
  match HS.sel h l with
  | Nil ->
      [l]
  | Cons next _ ->
      let refs = footprint h next (n - 1) in
      l :: refs
#reset-options

let rec modifies_disjoint_footprint
  (#a: Type)
  (#b: Type)
  (h: HS.mem)
  (l: t a)
  (n: nat)
  (r: ref b)
  (h' : HS.mem)
: Lemma
  (requires (
    well_formed h l n /\
    disjoint_from_list r (footprint h l n) /\
    HS.modifies_one (HS.frameOf r) h h' /\
    HS.modifies_ref (HS.frameOf r) (Set.singleton (HS.as_addr r)) h h'
  ))
  (ensures (
    well_formed h' l n /\
    footprint h' l n == footprint h l n
  ))
  (decreases n)
= match HS.sel h l with
  | Nil -> ()
  | Cons l' _ -> modifies_disjoint_footprint h l' (n - 1) r h'

let rec well_formed_distinct_lengths_disjoint
  #a1 #a2
  (c1: ref (cell a1))
  (c2: ref (cell a2))
  (n1: nat)
  (n2: nat)
  (h: HS.mem)
: Lemma
  (requires (
    well_formed h c1 n1 /\
    well_formed h c2 n2 /\
    n1 <> n2
  ))
  (ensures (
    disjoint c1 c2
  ))
  (decreases (n1 + n2))
= match HS.sel h c1, HS.sel h c2 with
  | Cons next1 _, Cons next2 _ ->
    well_formed_distinct_lengths_disjoint next1 next2 (n1 - 1) (n2 - 1) h
  | _ -> ()

let rec well_formed_gt_lengths_disjoint_from_list
  #a1 #a2
  (h: HS.mem)
  (c1: ref (cell a1))
  (c2: ref (cell a2))
  (n1: nat)
  (n2: nat)
: Lemma
  (requires (well_formed h c1 n1 /\ well_formed h c2 n2 /\ n1 > n2))
  (ensures (disjoint_from_list c1 (footprint h c2 n2)))
  (decreases n2)
= well_formed_distinct_lengths_disjoint c1 c2 n1 n2 h;
  if n2 = 0
  then ()
  else well_formed_gt_lengths_disjoint_from_list h c1 (Cons?.next (HS.sel h c2)) n1 (n2 - 1)

let well_formed_head_tail_disjoint
  #a
  (h: HS.mem)
  (c: ref (cell a))
  (n: nat)
: Lemma
  (requires (well_formed h c n))
  (ensures (let (hd :: tl) = footprint h c n in hd == c /\ disjoint_from_list c tl))
= if n = 0
  then ()
  else well_formed_gt_lengths_disjoint_from_list h c (Cons?.next (HS.sel h c)) n (n - 1)

let rec unused_in_well_formed_disjoint_from_list
  #a #b
  (h: HS.mem)
  (r: ref a)
  (l: ref (cell b))
  (n: nat)
: Lemma
  (requires (r `HS.unused_in` h /\ well_formed h l n))
  (ensures (disjoint_from_list r (footprint h l n)))
  (decreases n)
= if n = 0
  then ()
  else unused_in_well_formed_disjoint_from_list h r (Cons?.next (HS.sel h l)) (n - 1)

/// Finally, the pop operation. Our representation of linked lists is slightly
/// unusual, owing to the fact that we do not have null references, and
/// therefore represent the empty list as a reference to `Nil`. This means that
/// popping an element off the front of the list can be done by merely writing
/// the next cell in that reference. This is in contrast to the classic
/// representation using null pointers, which requires the client to pass a
/// pointer to a pointer, which is then filled with the address of the next
/// cell, or null if this was the last element in the list.

/// The code is straightforward and crucially relies on the call to the lemma
/// above. Note that at this stage we do not prove full functional correctness
/// of our implementation. Rather, we just state that the lengths is as
/// expected.

/// This version uses an erased integer n; we have to work a little bit to
/// hide/reveal the computationally-irrelevant length.
val pop: (#a: Type) -> (#n: G.erased nat) -> (l: t a) ->
  Stack (option a)
  (requires (fun h -> well_formed h l (G.reveal n)))
  (ensures (fun h0 v h1 ->
    let n = G.reveal n in
    match v with
    | None -> n = 0 /\ well_formed h1 l n
    | Some _ -> n > 0 /\ well_formed h1 l (n - 1)
  ))

let pop #a #n l =
  match !l with
  | Nil -> None
  | Cons next data ->
      let h0 = get () in
      l := !next;
      let h1 = get () in
      well_formed_head_tail_disjoint h0 l (G.reveal n);
      modifies_disjoint_footprint h0 next (G.reveal n - 1) l h1;
      Some data

val push: (#a: Type) -> (#n: G.erased nat) -> (l: t a) -> (x: a) ->
  ST unit
    (requires (fun h -> well_formed h l (G.reveal n)))
    (ensures (fun h0 () h1 -> well_formed h1 l (G.reveal n + 1)))

let push #a #n l x =
  let h0 = get () in
  let c: ref (cell a) = ralloc HS.root !l in
  unused_in_well_formed_disjoint_from_list h0 c l (G.reveal n);
  let h1 = get () in
  modifies_disjoint_footprint h0 l (G.reveal n) c h1;
  l := Cons c x;
  let h2 = get () in
  well_formed_head_tail_disjoint h0 l (G.reveal n);
  modifies_disjoint_footprint h1 c (G.reveal n) l h2


/// Connecting our predicate `well_formed` to the regular length function.
/// Note that this function takes a list whose length is unknown statically,
/// because of the existential quantification.
val length (#a: Type) (gn: G.erased nat) (l: t a): Stack UInt32.t
  (requires (fun h -> well_formed h l (G.reveal gn)))
  (ensures (fun h0 n h1 ->
    h0 == h1 /\
    U32.v n = G.reveal gn
  ))

/// Note that we could have as easily returned an option, but sometimes fatal
/// errors are just easier to handle for client code. The `C.String` module
/// provides facilities for dealing with constant C string literals. It reveals
/// that they are zero-terminated and allows looping over them if one wants to,
/// say, copy an immutable constant string into a mutable buffer.
let rec length #a gn l =
  match !l with
  | Nil ->
      0ul
  | Cons next _ ->
      let open U32 in
      let h = get () in
      let n = length (G.hide (G.reveal gn - 1)) next in
      if n = 0xfffffffful then begin
        C.String.(print !$"Integer overflow while computing length");
        C.exit 255l;
        0ul // dummy return value, this point is unreachable
      end else
        n +^ 1ul
  
val main: unit -> ST (Int32.t) (fun _ -> true) (fun _ _ _ -> true)
let main () =
  let l: ref (cell Int32.t) = ralloc HS.root Nil in
  push #Int32.t #(G.hide 0) l 1l;
  push #Int32.t #(G.hide 1) l 0l;
  match pop #Int32.t #(G.hide 2) l with
  | None -> 1l
  | Some x -> x
