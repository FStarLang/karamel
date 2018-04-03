module LinkedList1

module B = FStar.Buffer
module HS = FStar.HyperStack
module G = FStar.Ghost
module L = FStar.List.Tot
module U32 = FStar.UInt32

open FStar.HyperStack.ST

#set-options "--__no_positivity --use_two_phase_tc false"

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
/// enrich lists with a predicate that captures their length. This predicate
/// will be needed for any traversal of the list, in order to show termination.
/// Some points of interest:
/// - the absence of cycles does not suffice to guarantee termination, as the
///   number of references in the heap is potentially infinite;
/// - the heap model allows us to select without showing liveness, which allows
///   to de-couple the length predicate from the liveness predicate.
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

/// Note: all the ghost predicates and functions operate on a length of type
/// nat; the Ghost effect guarantees that the length can only be used at
/// run-time. Functions called at run-time will, conversely, use a length of
/// type `erased nat`, which states that the length is
/// computationally-irrelevant and can be safely removed from the resulting C
/// code via a combination of F* + KreMLin erasure.

/// When traversing a list `l` such that `list_has_length h l n`, it is often
/// the case that we recursively visit the Cons cell, passing `n - 1` for the
/// recursive call. This lemma ensures that Z3 can show that `n - 1` has type
/// `nat`.
let cons_nonzero_length #a (h: HS.mem) (c: ref (cell a)) (l: nat):
  Lemma
    (requires (list_has_length h c l /\ Cons? (HS.sel h c)))
    (ensures (l <> 0))
    [ SMTPat (list_has_length h c l); SMTPat (Cons? (HS.sel h c)) ] =
    ()

/// The contraposition of this lemma allows deriving that if two lengths are
/// different, then the corresponding references are disjoint.
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

/// For this example, we let all references live in the general region of the
/// heap. The `contains` predicate is needed by several lemmas from the heap
/// library, so we list it here.
///
/// The liveness predicate is `contains`: as an approximation, the underlying
/// heap model represents each region as a map from addresses to their values,
/// and contains asserts that the reference is in the domain of the map.
///
/// TODO: figure out why the predicate is called contains instead of
/// TODO: figure out why we need frameOf
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
/// TODO: there's a non-replayable hint here
#set-options "--max_ifuel 0 --max_fuel 1"
val footprint: (#a: Type) -> (h: HS.mem) -> (l: t a) -> (n: nat) -> Ghost (list (ref (cell a)))
  (requires (well_formed h l n))
  (ensures (fun refs ->
    let n_refs = L.length refs in
    n_refs = n /\
    (forall (i: nat). {:pattern (L.index refs i)}
      i < n ==> well_formed h (L.index refs i) (n - i))))
  (decreases n)

let rec footprint #a h l n =
  match HS.sel h l with
  | Nil ->
      []
  | Cons next _ ->
      let refs = footprint h next (n - 1) in
      l :: refs
#reset-options

/// There are several views of references; by default, references do not support
/// decidable equality, i.e. the heap model does not expose pointer comparisons.
/// One can, however, reason about equality of addresses (ghostly, i.e. in
/// proofs only) by using `HS.as_addr`. From two references having distinct
/// addresses, it follows that writing to one leaves the other untouched.

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
      forall (i: nat). // {:pattern well_formed h0 (L.index refs i) (n - i)}
        i < n ==> HS.as_addr head <> HS.as_addr (L.index refs i))
    ))
    (ensures (
      live h0 head /\
      Cons? (HS.sel h0 head) /\ (
      let next = Cons?.next (HS.sel h0 head) in
      let h1 = HS.upd h0 head (HS.sel h0 next) in
      well_formed h1 l n)
    ))
    (decreases n)
    [ SMTPat (well_formed #a h0 l n); SMTPat (Cons? (HS.sel h0 head)) ]

#set-options "--z3rlimit 40 --max_ifuel 0"
let rec pop_preserves_live #a h0 head l n =
  match HS.sel h0 l with
  | Nil -> ()
  | Cons l' _ ->
      pop_preserves_live h0 head l' (n - 1)

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
      pop_preserves_live #a h0 l next (G.reveal n - 1);
      Some data

val push: (#a: Type) -> (#n: G.erased nat) -> (l: t a) -> (x: a) ->
  ST unit
    (requires (fun h -> well_formed h l (G.reveal n)))
    (ensures (fun h0 () h1 -> well_formed h1 l (G.reveal n + 1)))

let push #a #n l x =
  let c: ref (cell a) = ralloc HS.root !l in
  // need to write a lemma that states that allocation preserves the live
  // predicate for lists
  l := Cons c x;
  admit ()


/// Connecting our predicate `list_has_length` to the regular length function.
/// Note that this function takes a list whose length is unknown statically,
/// because of the existential quantification.
/// TODO: figure out why the `assert` is needed.
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
      let h = get () in
      assert (list_has_length h l 0);
      0ul
  | Cons next _ ->
      let open U32 in
      let h = get () in
      let n = length (G.hide (G.reveal gn - 1)) next in
      if n = 0xfffffffful then begin
        C.String.(print !$"Integer overflow while computing length");
        C.exit 255l;
        0ul
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
