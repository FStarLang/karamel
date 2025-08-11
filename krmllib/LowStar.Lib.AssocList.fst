module LowStar.Lib.AssocList

/// A Low*, stateful associative list that exposes a map-like interface.

module B = LowStar.Buffer
module HS = FStar.HyperStack
module G = FStar.Ghost
module ST = FStar.HyperStack.ST

module M = FStar.Map
module LL2 = LowStar.Lib.LinkedList2
module LL1 = LowStar.Lib.LinkedList

open FStar.HyperStack.ST
open LowStar.BufferOps

#set-options "--fuel 0 --ifuel 0"

/// Types, invariants, footprint
/// ----------------------------

/// We prefer the packed representation that is in general easier to use and will
/// look at the underlying predicate-based representation from LL1 only when
/// strictly needed.
let t k v =
  LL2.t (k & v)

/// Functions suffixed with an underscore operate on either LL1 or raw lists
/// while those without operate on LL2.
val v_: #t_k:eqtype -> #t_v:Type0 -> l:list (t_k & t_v) -> Tot (map t_k t_v)
let v_ #_ #t_v l =
  List.Tot.fold_right (fun (k, v) m -> M.upd m k (Some v)) l (M.const (None #t_v))

/// Reflecting a stateful, imperative map as a functional one in a given heap.
let v #_ #_ h ll =
  let l = LL2.v h ll in
  v_ l

let invariant #_ #_ h ll =
  LL2.invariant h ll

// No longer needed in the fsti.
val footprint: #t_k:eqtype -> #t_v:Type0 -> h:HS.mem -> ll:t t_k t_v -> Ghost B.loc
  (requires invariant h ll)
  (ensures fun _ -> True)

let footprint #_ #_ h ll =
  LL2.footprint h ll

let region_of #_ #_ ll =
  LL2.region_of ll

let frame #_ #_ ll _ h0 _ =
  LL2.footprint_in_r h0 ll

val footprint_in_r: #t_k:eqtype -> #t_v:Type0 -> h0:HS.mem -> ll:t t_k t_v -> Lemma
  (requires
    invariant h0 ll)
  (ensures
    B.(loc_includes (region_of ll) (footprint h0 ll)))
  [ SMTPat (footprint h0 ll) ]

let footprint_in_r #_ #_ h0 ll =
  LL2.footprint_in_r h0 ll

#push-options "--fuel 1"
let create_in #_ #_ r =
  LL2.create_in r
#pop-options

/// Find
/// ----

/// Proper recursion can only be done over the LL1.t type (unpacked representation).
val find_ (#t_k: eqtype) (#t_v: Type0) (hd: LL1.t (t_k & t_v)) (l: G.erased (list (t_k & t_v))) (k: t_k):
  Stack (option t_v)
    (requires fun h0 ->
      LL1.well_formed h0 hd l /\
      LL1.invariant h0 hd l)
    (ensures fun h0 x h1 ->
      let m: map t_k t_v = v_ l in
      h0 == h1 /\
      x == M.sel m k)

#push-options "--fuel 1 --ifuel 1"
let rec find_ #_ #_ hd l k =
  if B.is_null hd then
    None
  else
    let cell = !* hd in
    if fst cell.LL1.data = k then
      Some (snd cell.LL1.data)
    else
      find_ cell.LL1.next (List.Tot.tl l) k
#pop-options


let find #_ #_ ll k =
  find_ !*ll.LL2.ptr !*ll.LL2.v k

/// Adding elements
/// ---------------

#push-options "--fuel 1"
let add #_ #_ ll k x =
  LL2.push ll (k, x)
#pop-options

/// Removing elements
/// -----------------

/// This one is tricky to state so temporarily disabled. I'm trying to offer a
/// shadowing API that allows revealing the previous binding (if any) when the
/// most recent one is remoed. However, as it stands, the precondition is not
/// strong enough to conclude that just popping the first occurrence of key
/// ``k`` in the list yields ``m``.
///
/// I'm unsure on how to do that cleanly and abstractly without revealing to the
/// client the underlying associative-list nature of the map abstraction, so
/// disabling for now.
///
(*val remove_one (#t_k: eqtype)
  (#t_v: Type0)
  (ll: t t_k t_v)
  (k: t_k)
  (x: G.erased t_v)
  (m: G.erased (map t_k t_v)):
  ST unit
    (requires fun h0 ->
      invariant h0 ll /\
      // TODO: file bug to figure why auto-reveal doesn't work (also in post-condition)
      v h0 ll == M.upd m k (Some (G.reveal x)))
    (ensures fun h0 _ h1 ->
      B.modifies (footprint h0 ll) h0 h1 /\
      v h1 ll == G.reveal m)*)

val remove_all_ (#t_k: eqtype) (#t_v: Type0) (hd: LL1.t (t_k & t_v)) (l: G.erased (list (t_k & t_v))) (k: t_k):
  ST (LL1.t (t_k & t_v) & G.erased (list (t_k & t_v)))
    (requires fun h0 ->
      LL1.well_formed h0 hd l /\
      LL1.invariant h0 hd l)
    (ensures fun h0 (hd', l') h1 ->
      LL1.well_formed h1 hd' l' /\
      LL1.invariant h1 hd' l' /\
      B.(loc_includes (LL1.footprint h0 hd l) (LL1.footprint h1 hd' l')) /\
      B.modifies (LL1.footprint h0 hd l) h0 h1 /\
      v_ l' == M.upd (v_ l) k None)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
let rec remove_all_ #t_k #t_v hd l k =
  let h0 = ST.get () in
  if B.is_null hd then begin
    M.lemma_equal_intro (v_ l) (M.upd (v_ l) k None);
    hd, l
  end else begin
    let cell = !*hd in
    let { LL1.data; LL1.next } = cell in
    let k', v = data in
    if k = k' then begin
      B.free hd;
      let h1 = ST.get () in
      LL1.frame next (List.Tot.tail l) (B.loc_addr_of_buffer hd) h0 h1;
      let hd', l' = remove_all_ next (List.Tot.tail l) k in
      M.lemma_equal_intro (v_ l') (M.upd (v_ l) k None);
      hd', l'
    end else begin
      let hd', l' = remove_all_ next (List.Tot.tail l) k in
      let h1 = ST.get () in
      hd *= { LL1.data; LL1.next = hd' };
      let h2 = ST.get () in
      LL1.frame hd' l' (B.loc_addr_of_buffer hd) h1 h2;
      M.lemma_equal_intro (v_ ((k', v) :: l')) (M.upd (v_ l) k None);
      assert B.(loc_disjoint (loc_buffer hd) (LL1.footprint h2 hd' l'));
      assert (B.live h2 hd /\ B.length hd == 1);
      assert (LL1.well_formed h2 hd' l');
      assert (LL1.invariant h2 hd (data :: l'));
      hd, G.hide ((k', v) :: l')
    end
  end
#pop-options

#push-options "--fuel 1"
let remove_all #_ #_ ll k =
  let open LL2 in
  let hd, v = remove_all_ !*ll.ptr !*ll.v k in
  ll.ptr *= hd;
  ll.v *= v
#pop-options

/// Clearing (resetting)
/// --------------------

#push-options "--fuel 1"
let clear #_ #_ ll =
  LL2.clear ll
#pop-options

/// Freeing the resource
/// --------------------

let free #_ #_ ll =
  LL2.free ll
