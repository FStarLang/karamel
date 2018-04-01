module LinkedList

module B = FStar.Buffer
module HS = FStar.HyperStack
module G = FStar.Ghost
module L = FStar.List.Tot

open FStar.HyperStack.ST

#set-options "--__no_positivity"

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

/// Since linked lists go through a reference for indirection purposes, we
/// enrich lists with a predicate that captures their length.
let rec list_has_length #a (h: HS.mem) (c: t a) (l: nat):
  GTot bool (decreases l)
=
  match HS.sel h c with
  | Nil -> l = 0
  | Cons next _ ->
      if l = 0 then
        false
      else
        list_has_length h next (l - 1)

/// Note: a tempting solution might be to enrich the type of cells with an
/// erased length that contains the "built-in" existentially quantified,
/// proof-only, computationally-irrelevant length. This would, in turn,
/// guarantee erasure by KreMLin and we would recover the type of linked lists
/// that we hope for. This is tedious in practice, as the normalizer does not
/// reduce underneath an `erased t`, leading to considerable type-checking
/// difficulties.

/// This lemma ensures that when matching on a Cons cell, then recursively
/// calling something on length (l - 1), we get automatically that (l - 1) is
/// nat.
let cons_nonzero_length #a (h: HS.mem) (c: ref (cell a)) (l: nat):
  Lemma
    (requires (list_has_length h c l /\ Cons? (HS.sel h c)))
    (ensures (l <> 0))
    [ SMTPat (list_has_length h c l); SMTPat (Cons? (HS.sel h c)) ] =
    ()

let rec length_injective #a (h: HS.mem) (c: ref (cell a)) (l1 l2: nat):
  Lemma
    (requires (list_has_length h c l1 /\ list_has_length h c l2))
    (ensures (l1 = l2))
    (decreases l1)
    [ SMTPat (list_has_length h c l1); SMTPat (list_has_length h c l2) ] =
  match HS.sel h c with
  | Nil -> ()
  | Cons next _ ->
      // Without `cons_nonzero_length`, we would need assert (l1 <> 0)
      length_injective h next (l1 - 1) (l2 - 1)

/// A predicate that states that a single reference (the cell) is live.
/// TODO: figure out why the predicate is called contains instead of live
/// TODO: figure out why we need frameOf (see note to Aseem)
let cell_is_live #a (h: HS.mem) (c: t a) =
  HS.frameOf c = HS.root /\
  HS.contains h c

/// This predicate states that all the cells are live. It relies on
/// `list_has_length` for its termination.
/// TODO: figure out why `cell_is_live h l /\ (match ...)` doesn't work.
let rec list_is_live #a #n (h: HS.mem) (l: t a {list_has_length h l n}):
  Tot Type (decreases n)
=
  match HS.sel h l with
  | Nil ->
      cell_is_live h l /\
      True
  | Cons next _ ->
      cell_is_live h l /\
      list_is_live #a #(n - 1) h next

/// Thus, a well-formed list is both paired with a predicate for its length, and
/// states that are the list cells are live in the current heap.
let well_formed #a (h: HS.mem) (l: t a) (n: nat) =
  list_has_length h l n /\ list_is_live #a #n h l

/// This form will rarely turn out to be useful, except perhaps for user code.
/// Indeed, we most often want to tie the length of the list in the final state
/// with its length in the original state.
let live #a (h: HS.mem) (l: t a) =
  exists n. well_formed #a h l n


/// As we start proving some degree of functional correctness, we will have to
/// reason about non-interference, and state that some operations do not modify
/// the footprint of a given list.
/// TODO: proper patterns for quantifiers!
#set-options "--max_ifuel 0 --max_fuel 1"
val footprint: (#a: Type) -> (h: HS.mem) -> (l: t a) -> (n: nat) -> Ghost (list (ref (cell a)))
  (requires (well_formed h l n))
  (ensures (fun refs ->
    let n_refs = L.length refs in
    n_refs = n /\
    (forall (i: nat). i < n ==> well_formed h (L.index refs (n - 1 - i)) (i + 1))))
  (decreases n)

let rec footprint #a h l n =
  match HS.sel h l with
  | Nil ->
      []
  | Cons next _ ->
      let refs = footprint h next (n - 1) in
      l :: refs
#reset-options

/// All the reasoning about the pop operation is done in this lemma. If `head`
/// is not found in the footprint of `l`, then the specific write we perform for
/// pop (we could be more generic!) leaves the two essential predicates
/// untouched for l.
/// TODO: this proof is slow / investigate
val pop_preserves_live: (#a: Type) -> (h0: HS.mem) -> (head: ref (cell a)) -> (l: t a) -> (n: nat) ->
  Lemma
    (requires (
      live h0 head /\
      Cons? (HS.sel h0 head) /\
      well_formed h0 l n /\ (
      let refs = footprint h0 l n in
      forall (i: nat). i < n ==> HS.as_addr head <> HS.as_addr (L.index refs i)
    )))
    (ensures (
      live h0 head /\
      Cons? (HS.sel h0 head) /\ (
      let next = Cons?.next (HS.sel h0 head) in
      let h1 = HS.upd h0 head (HS.sel h0 next) in
      well_formed h1 l n
    )))
    (decreases n)
    [ SMTPat (well_formed #a h0 l n); SMTPat (Cons? (HS.sel h0 head)) ]

#set-options "--z3rlimit 40 --max_ifuel 0"
let rec pop_preserves_live #a h0 head l n =
  match HS.sel h0 l with
  | Nil -> ()
  | Cons l' _ ->
      pop_preserves_live h0 head l' (n - 1)

/// Finally, the pop operation. The code is straightforward and crucially relies
/// on the call to the lemma above. Note that at this stage we do not prove full
/// functional correctness of our implementation. Rather, we just state that the
/// lengths is as expected.
/// TODO: move this code to use an erased integer... but merely computing n - 1
/// below behind an erased type is tedious.
val pop: (#a: Type) -> (#n: nat) -> (l: t a) ->
  ST (option a)
  (requires (fun h -> well_formed h l n))
  (ensures (fun h0 v h1 ->
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
      pop_preserves_live #a h0 l next (n - 1);
      Some data

/// Purely a test function to see some actual code.
let test_pop #n (l: t UInt32.t): ST UInt32.t
  (requires (fun h -> well_formed h l n))
  (ensures (fun _ _ _ -> true)) =
  match pop #UInt32.t #n l with
  | None -> 0ul
  | Some x -> x
