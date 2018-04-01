module LinkedList

module B = FStar.Buffer
module HS = FStar.HyperStack
module G = FStar.Ghost

open FStar.HyperStack.ST

/// We revisit the classic example of lists, but in a low-level setting, using
/// linked lists. This first version uses `ref`, the type of references that are
/// always live.
noeq
type linked_cell (a: Type0) =
  | Nil: linked_cell a
  | Cons:
      next: ref (linked_cell a) ->
      data: a ->
      linked_cell a

/// Since linked lists go through a reference for indirection purposes, we
/// enrich lists with a predicate that captures their length.
let rec cell_has_length #a (h: HS.mem) (c: linked_cell a) (l: nat): GTot bool (decreases l) =
  match c with
  | Nil -> l = 0
  | Cons next _ ->
      if l = 0 then
        false
      else
        cell_has_length h (HS.sel h next) (l - 1)

/// This lemma ensures that when matching on a Cons cell, then recursively
/// calling something on length (l - 1), we get automatically that (l - 1) is
/// nat.
let cons_nonzero_length #a (h: HS.mem) (c: linked_cell a) (l: nat):
  Lemma
    (requires (cell_has_length h c l /\ Cons? c))
    (ensures (l <> 0))
    [ SMTPat (cell_has_length h c l); SMTPat (Cons? c) ] =
    ()

let rec length_unique #a (h: HS.mem) (c: linked_cell a) (l1 l2: nat):
  Lemma
    (requires (cell_has_length h c l1 /\ cell_has_length h c l2))
    (ensures (l1 = l2))
    (decreases l1)
    [ SMTPat (cell_has_length h c l1); SMTPat (cell_has_length h c l2) ] =
  match c with
  | Nil -> ()
  | Cons next _ ->
      // Without `cons_nonzero_length`, we would need assert (l1 <> 0)
      length_unique h (HS.sel h next) (l1 - 1) (l2 - 1)

/// We pass lists by reference; so, a linked list is just a reference to a cell.
type linked_list (a: Type0) =
  ref (linked_cell a)

/// This predicate states that are the cells are live. It relies on
/// `cell_has_length` for its termination.
/// TODO: figure out why the predicate is called contains instead of live
let rec cell_is_live #a #n (h: HS.mem) (c: linked_cell a {cell_has_length h c n})
: Tot Type (decreases n)
=
  match c with
  | Nil ->
      True
  | Cons next _ ->
      HS.frameOf next = HS.root /\
      HS.contains h next /\
      cell_is_live #a #(n - 1) h (HS.sel h next)

/// A live list is a live reference, that points to a live series of cells. We
/// state that there exists an (unknown) length for this list.
let list_is_live #a (h: HS.mem) (l: linked_list a) =
  HS.frameOf l = HS.root /\ HS.contains h l /\ (
  let c = HS.sel h l in
  exists n. cell_has_length h c n /\ cell_is_live #a #n h c)

let list_next_live #a (h: HS.mem) (l: linked_list a):
  Lemma
    (requires (list_is_live h l /\ Cons? (HS.sel h l)))
    (ensures (list_is_live h (Cons?.next (HS.sel h l))))
=
  ()

let list_next_disjoint #a (h: HS.mem) (l: linked_list a):
  Lemma
    (requires (list_is_live h l /\ Cons? (HS.sel h l)))
    (ensures (HS.as_addr l <> HS.as_addr (Cons?.next (HS.sel h l))))
=
  ()

val pop: (#a: Type) -> (l: linked_list a) ->
  ST (option a)
  (requires (fun h -> list_is_live h l))
  (ensures (fun h0 _ h1 -> True))//list_is_live h1 l))
let pop #a l =
  match !l with
  | Nil -> None
  | Cons next data ->
      let h0 = get () in
      list_next_disjoint h0 l;
      list_next_live h0 l;
      assert (list_is_live h0 l);
      assert (list_is_live h0 next);
      l := !next;
      let h1 = get () in
      assert (HS.sel h0 next == HS.sel h1 next);
      assert (list_is_live h1 next);
      Some data
