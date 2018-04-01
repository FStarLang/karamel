module LinkedList

module B = FStar.Buffer
module HS = FStar.HyperStack
module G = FStar.Ghost
module L = FStar.List.Tot

open FStar.HyperStack.ST

/// We revisit the classic example of lists, but in a low-level setting, using
/// linked lists. This first version uses `ref`, the type of references that are
/// always live. However, we don't cheat and recall liveness "for free".
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

/// This form will rarely turn out to be useful, except perhaps for user code.
/// Indeed, we most often want to tie the length of the list in the final state
/// with its length in the original state.
let live #a (h: HS.mem) (l: t a) =
  exists n. list_has_length h l n /\ list_is_live #a #n h l


/// As we start proving some degree of functional correctness, we will have to
/// reason about non-interference, and state that some operations do not modify
/// the footprint of a given list.
/// TODO: proper patterns for quantifiers!
#set-options "--max_ifuel 0 --max_fuel 1"
val footprint: (#a: Type) -> (#n: nat) -> (h: HS.mem) -> (l: t a) -> Ghost (list (ref (cell a)))
  (requires (
    list_has_length h l n /\
    list_is_live #a #n h l
  ))
  (ensures (fun refs ->
    let n_refs = L.length refs in
    n_refs = n /\
    (forall (i: nat). i < n ==>
      list_has_length h (L.index refs (n - 1 - i)) (i + 1) /\
      cell_is_live #a h (L.index refs (n - 1 - i)))
  ))

let rec footprint #a #n h l =
  match HS.sel h l with
  | Nil ->
      []
  | Cons next _ ->
      let refs = footprint #a #(n - 1) h next in
      l :: refs
#reset-options

/// An intermediary lemma, for sanity (it is currently unused): the head is
/// disjoint from anything found in the footprint of the tail. The
/// list_has_length predicate provides an easy contradiction if it were the
/// case.
/// TODO: pattern!
let list_next_disjoint_i (#a: Type) (#n: nat) (h: HS.mem) (l: t a) (i: nat):
  Lemma
    (requires (
      list_has_length h l n /\
      list_is_live #a #n h l /\
      i < n - 1 /\
      Cons? (HS.sel h l)))
    (ensures (
      let next = Cons?.next (HS.sel h l) in
      let refs = footprint #a #(n - 1) h next in
      HS.as_addr l <> HS.as_addr (L.index refs i)
    ))
=
  ()

/// All the reasoning about the pop operation is done in this lemma. If `head`
/// is not found in the footprint of `l`, then the specific write we perform for
/// pop (we could be more generic!) leaves the two essential predicates
/// untouched for l.
val pop_preserves_live: (#a: Type) -> (#n: nat) -> (h0: HS.mem) -> (head: ref (cell a)) -> (l: t a) ->
  Lemma
    (requires (
      live h0 head /\
      Cons? (HS.sel h0 head) /\
      list_has_length h0 l n /\
      list_is_live #a #n h0 l /\ (
      let refs = footprint #a #n h0 l in
      forall (i: nat). i < n ==> HS.as_addr head <> HS.as_addr (L.index refs i)
    )))
    (ensures (
      live h0 head /\
      Cons? (HS.sel h0 head) /\ (
      let next = Cons?.next (HS.sel h0 head) in
      let h1 = HS.upd h0 head (HS.sel h0 next) in
      list_has_length h1 l n /\
      list_is_live #a #n h1 l
    )))
    (decreases n)
    [ SMTPat (list_is_live #a #n h0 l); SMTPat (Cons? (HS.sel h0 head)) ]

#set-options "--z3rlimit 40 --max_ifuel 0"
let rec pop_preserves_live #a #n h0 head l =
  match HS.sel h0 l with
  | Nil -> ()
  | Cons l' _ ->
      pop_preserves_live #a #(n - 1) h0 head l'

val pop: (#a: Type) -> (#n: nat) -> (l: t a) ->
  ST (option a)
  (requires (fun h -> list_has_length h l n /\ list_is_live #a #n h l))
  (ensures (fun h0 v h1 ->
    match v with
    | None -> list_has_length h1 l n /\ list_is_live #a #n h1 l
    | Some _ -> n > 0 /\ list_has_length h1 l (n - 1) /\ list_is_live #a #(n - 1) h1 l
  ))

let pop #a #n l =
  match !l with
  | Nil -> None
  | Cons next data ->
      let h0 = get () in
      l := !next;
      pop_preserves_live #a #(n - 1) h0 l next;
      Some data
