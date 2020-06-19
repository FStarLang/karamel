module AssocList

/// We are relying on an associative list to implement our imperative map but
/// this will be upgraded to a hash table that offers the same interface.
module IM = LowStar.Lib.AssocList
module M = FStar.Map
module B = LowStar.Buffer
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module LL1 = LowStar.Lib.LinkedList
module LL2 = LowStar.Lib.LinkedList2
module G = FStar.Ghost

open LowStar.BufferOps
open FStar.HyperStack.ST

#set-options "--fuel 0 --ifuel 0"

/// Definition of types. I'm aiming to capture the essence of the Wireguard use case.

// Simple representation of noise_handshake. One extra indirection compared to
// wireguard, alas.
let handshake_state = B.buffer UInt8.t

noeq
// Simplified equivalent of wg_peer.
type peer = {
  hs: handshake_state;
  id: UInt64.t;
  device: B.pointer device;
}

// Simplified equivalent of wg_device.
and device = {
  peers: LL2.t peer;
  // I'm doing pointer sharing here so that the peers in peer_of_id are pointing
  // directly to the list cells in the linked list, like in WireGuard
  peer_of_id: IM.t UInt64.t (LL1.t peer);
  r: HS.rid;
  // Region for the spine of the linked list.
  r_peers: HS.rid;
  // Region for the imperative map.
  r_peer_of_id: HS.rid;
  // Region for the payload of each list cell.
  r_peers_payload: HS.rid;
}

/// A single peer
/// -------------
let peer_invariant (h: HS.mem) (p: peer) =
  // Sample invariant for the handshake_state -- to be filled out with something more realistic.
  B.live h p.hs /\
  B.length p.hs == 8 /\
  B.freeable p.hs /\
  // Back-pointer invariant.
  B.live h p.device /\
  B.freeable p.device /\
  B.loc_disjoint (B.loc_addr_of_buffer p.hs) (B.loc_addr_of_buffer p.device)
  // JP: should this be strengthened to say that this peer is the one found in peer_of_id via p.device?

let peer_footprint (p: peer) =
  B.loc_addr_of_buffer p.hs `B.loc_union`
  B.loc_addr_of_buffer p.device

/// Properties of the payload of the linked list
/// --------------------------------------------

// Cannot use List.Tot.fold_right because GTot / Tot effect mistmatch
//
// IMPORTANT: the footprint themselves are not heap-dependent, otherwise, there
// would have to be a framing lemma for the footprint itself.

// If a peer needs to contain some data structure, for instance a linked list,
// then it can be done in the following way with a static footprint:
// - the peer contains an rid
// - the invariant states that each peer's rid is a child of r_peer_payload,
//   that the peers' rids are mutually disjoint, and that the rid is, say, the
//   region_of the LL2.t
// This yields non heap-dependent predicates which keeps complexity under control.
let rec peers_footprint (ps: list peer): GTot B.loc =
  allow_inversion (list peer);
  match ps with
  | [] -> B.loc_none
  | p :: ps -> peer_footprint p `B.loc_union` peers_footprint ps

let rec peers_disjoint (ps: list peer) =
  allow_inversion (list peer);
  match ps with
  | [] -> True
  | p :: ps ->
      peer_footprint p `B.loc_disjoint` peers_footprint ps /\
      peers_disjoint ps

let rec peers_invariants (h: HS.mem) (r: HS.rid) (ps: list peer) =
  allow_inversion (list peer);
  match ps with
  | [] -> True
  | p :: ps ->
      B.(loc_all_regions_from false r `loc_includes` peer_footprint p) /\
      peer_invariant h p /\
      peers_invariants h r ps

let peers_invariant (h: HS.mem) (r: HS.rid) (ps: list peer) =
  peers_disjoint ps /\
  peers_invariants h r ps

// TODO: ids are pairwise disjoint, to facilitate insertion

/// Relating peer_of_id to a given list of peers
/// --------------------------------------------

let rec peer_by_id (id: UInt64.t) (ps: list peer) =
  allow_inversion (list peer);
  match ps with
  | p :: ps ->
      if p.id = id then
        Some p
      else
        peer_by_id id ps
  | [] ->
      None

let rec cell_by_id (h: HS.mem) (id: UInt64.t) (ps: list (B.pointer (LL1.cell peer))):
  GTot (option (B.pointer (LL1.cell peer)))
=
  allow_inversion (list (B.pointer (LL1.cell peer)));
  match ps with
  | p :: ps ->
      if (B.deref h p).LL1.data.id = id then
        Some p
      else
        cell_by_id h id ps
  | [] ->
      None

let peer_of_id_in_peers (h: HS.mem) (d: device) (i: UInt64.t): Ghost Type
  (requires LL2.invariant h d.peers)
  (ensures fun _ -> True)
=
  let m = IM.v h d.peer_of_id in
  let p = peer_by_id i (LL2.v h d.peers) in
  // Note: going via cells has numerous advantages. First, we can switch back
  // and forth between the footprint view and the cells view, and we have
  // auxiliary lemmas for that here. Second, clients can derive useful
  // properties by doing a induction on cells (which will reveal it computes the
  // same thing as LL2.v).
  let cell = cell_by_id h i (LL2.cells h d.peers) in
  match M.sel m i with
  | None ->
      // peer_of_id is an incomplete map -- it may not contain pointers to all elements in peer_of_id
      // if we wanted to make is so, we'd have to have p == None here
      True
  | Some ptr ->
      // Much simpler than before! Clients can use cell_by_id is peer_by_id to
      // derive stuff like, the peer found in the table verifies its invariant.
      Some? cell /\
      ptr == Some?.v cell

/// Back pointers invariant
/// -----------------------

let rec peers_back (h: HS.mem) (d: device) (ps: list peer) =
  allow_inversion (list peer);
  match ps with
  | p :: ps ->
      B.deref h p.device == d /\
      peers_back h d ps
  | [] ->
      True

/// Global invariant on the device
/// ------------------------------

unfold
let invariant (h: HS.mem) (d: device) =
  ST.is_eternal_region d.r /\
  ST.is_eternal_region d.r_peers /\
  ST.is_eternal_region d.r_peer_of_id /\
  ST.is_eternal_region d.r_peers_payload /\

  HS.extends d.r_peers d.r /\
  HS.extends d.r_peer_of_id d.r /\
  HS.extends d.r_peers_payload d.r /\

  HS.parent d.r_peers == d.r /\
  HS.parent d.r_peer_of_id == d.r /\
  HS.parent d.r_peers_payload == d.r /\

  B.(loc_disjoint (loc_all_regions_from false d.r_peers) (loc_all_regions_from false d.r_peer_of_id)) /\
  B.(loc_disjoint (loc_all_regions_from false d.r_peers) (loc_all_regions_from false d.r_peers_payload)) /\
  B.(loc_disjoint (loc_all_regions_from false d.r_peer_of_id) (loc_all_regions_from false d.r_peers_payload)) /\

  d.peers.LL2.r == d.r_peers /\
  IM.region_of d.peer_of_id == B.loc_all_regions_from false d.r_peer_of_id /\

  LL2.invariant h d.peers /\
  IM.invariant h d.peer_of_id /\
  peers_invariant h d.r_peers_payload (LL2.v h d.peers) /\
  // This is one more fact (like peer_footprint_in) that should be readily
  // available, but that cannot be derived automatically since it involves
  // inductive reasoning on the list of peers. We therefore stash it in the
  // invariant.
  B.(loc_includes (loc_all_regions_from false d.r_peers_payload) (peers_footprint (LL2.v h d.peers))) /\

  peers_back h d (LL2.v h d.peers) /\
  (forall (i: UInt64.t). {:pattern peer_of_id_in_peers h d i }
    peer_of_id_in_peers h d i) /\
  True

#push-options "--fuel 1"
/// Technicality: just like for LL1 (see comment there), since the footprint of
/// the payload of the peers is recursive, we don't automatically get
/// disjointness of fresh allocations w.r.t. peers_footprint which is a drag.
/// So, clients have to manually call this lemma.
let rec peer_footprint_in (h: HS.mem) (r: HS.rid) (ps: list peer): Lemma
  (requires peers_invariant h r ps)
  (ensures B.loc_in (peers_footprint ps) h)
=
  let _ = allow_inversion (list peer) in
  match ps with
  | [] -> ()
  | p :: ps ->
      assert (B.loc_in (peer_footprint p) h);
      peer_footprint_in h r ps
#pop-options

/// Framing lemmas
/// --------------
///
/// Since the list of peers is a recursive data structure, everything has to be framed manually.

#push-options "--fuel 1 --ifuel 1"
let rec frame_peers_back (l: B.loc) (h0 h1: HS.mem) (d: device) (ps: list peer): Lemma
  (requires
    B.(loc_disjoint l (loc_all_regions_from false d.r_peers_payload)) /\
    peers_invariants h0 d.r_peers_payload ps /\
    B.modifies l h0 h1 /\
    peers_back h0 d ps)
  (ensures
    peers_back h1 d ps)
=
  match ps with
  | [] ->
      ()
  | p :: ps ->
      frame_peers_back l h0 h1 d ps

let rec frame_peers_invariants (r_payload: HS.rid) (l: LL1.t peer) (n: list peer) (r: B.loc) (h0 h1: HS.mem): Lemma
  (requires (
    LL1.well_formed h0 l n /\
    peers_invariants h0 r_payload n /\
    B.(loc_disjoint r (peers_footprint n)) /\
    B.modifies r h0 h1
  ))
  (ensures (
    peers_invariants h1 r_payload n
  ))
  (decreases n)
=
  if B.g_is_null l then
    ()
  else
    let p = List.Tot.hd n in
    let ps = List.Tot.tl n in
    frame_peers_invariants r_payload (B.deref h0 l).LL1.next (List.Tot.tl n) r h0 h1

#pop-options

/// A helper lemma for clients.
#push-options "--fuel 1 --ifuel 1"
let rec peer_by_id_invariant (h: HS.mem) (r: HS.rid) (ps: list peer) (p: peer) (id: UInt64.t): Lemma
  (requires
    peers_invariant h r ps /\
    Some p == peer_by_id id ps)
  (ensures
    B.(loc_all_regions_from false r `loc_includes` peer_footprint p) /\
    peer_invariant h p)
=
  match ps with
  | p' :: ps' ->
      if p'.id = id then
        ()
      else
        peer_by_id_invariant h r ps' p id
#pop-options

/// Stateful API
/// ------------

#push-options "--fuel 1"
let create_in (r: HS.rid): ST device
  (requires fun h0 ->
    ST.is_eternal_region r)
  (ensures fun h0 d h1 ->
    invariant h1 d /\
    B.(modifies loc_none h0 h1) /\
    IM.v h1 d.peer_of_id == M.const None /\
    LL2.v h1 d.peers == [] /\
    d.r == r)
=
  let r_peers = ST.new_region r in
  let r_peer_of_id = ST.new_region r in
  let r_peers_payload = ST.new_region r in
  let peers = LL2.create_in r_peers in
  let peer_of_id = IM.create_in r_peer_of_id in
  { peers; peer_of_id; r; r_peers; r_peer_of_id; r_peers_payload }
#pop-options

#push-options "--fuel 1 --ifuel 1"
let rec free_peer_list (r_spine: HS.rid) (r_peers_payload: HS.rid) (hd: LL1.t peer) (l: G.erased (list peer)):
  ST unit
    (requires fun h0 ->
      peers_invariant h0 r_peers_payload l /\
      B.(loc_disjoint (loc_all_regions_from false r_spine) (loc_all_regions_from false r_peers_payload)) /\
      LL1.well_formed h0 hd l /\
      B.(loc_includes (loc_all_regions_from false r_spine) (LL1.footprint h0 hd l)) /\
      LL1.invariant h0 hd l)
    (ensures fun h0 _ h1 ->
      B.(modifies (loc_all_regions_from false r_peers_payload) h0 h1))
=
  if B.is_null hd then
    ()
  else
    let { LL1.data; LL1.next } = !* hd in
    let h0 = ST.get () in
    B.free data.device;
    B.free data.hs;
    let h1 = ST.get () in
    LL1.frame next (List.Tot.tl l) B.(loc_all_regions_from false r_peers_payload) h0 h1;
    frame_peers_invariants r_peers_payload next (List.Tot.tl l)
      B.(loc_addr_of_buffer data.device `loc_union` loc_addr_of_buffer data.hs) h0 h1;
    free_peer_list r_spine r_peers_payload next (List.Tot.tl l)
#pop-options

val free_ (d: device): ST unit
  (requires fun h0 ->
    invariant h0 d)
  (ensures fun h0 _ h1 ->
    B.(modifies (loc_all_regions_from false d.r) h0 h1))

let free_ d =
  let h0 = ST.get () in
  free_peer_list d.r_peers d.r_peers_payload (!* d.peers.LL2.ptr) (!* d.peers.LL2.v);
  let h1 = ST.get () in
  LL2.frame_region d.peers (B.loc_all_regions_from false d.r_peers_payload) h0 h1;
  LL2.footprint_in_r h1 d.peers;
  assert B.(loc_includes (loc_all_regions_from false d.r_peers) (LL2.footprint h1 d.peers));
  LL2.free d.peers;
  let h2 = ST.get () in
  assert (B.modifies (B.loc_all_regions_from false d.r_peers) h1 h2);
  assert (IM.region_of d.peer_of_id == B.loc_all_regions_from false d.r_peer_of_id);
  IM.frame d.peer_of_id (B.loc_all_regions_from false d.r_peers) h1 h2;
  assert (IM.invariant h2 d.peer_of_id);
  IM.free d.peer_of_id

/// Some helper lemmas
/// ------------------


#push-options "--fuel 1 --ifuel 1"
let rec cell_by_id_is_peer_by_id (h: HS.mem) (i: UInt64.t) (ll: LL1.t peer) (l: list peer): Lemma
  (requires
    LL1.well_formed h ll l /\
    LL1.invariant h ll l)
  (ensures (
    let p = peer_by_id i l in
    let c = cell_by_id h i (LL1.cells h ll l) in
    (Some? c <==> Some? p) /\
    (Some? c ==>
      (B.deref h (Some?.v c)).LL1.data == (Some?.v p))))
  (decreases l)
=
  if B.g_is_null ll then
    ()
  else
    let p = peer_by_id i l in
    let c = cell_by_id h i (LL1.cells h ll l) in
    cell_by_id_is_peer_by_id h i (B.deref h ll).LL1.next (List.Tot.tl l)

let rec cell_by_id_depends_only_on_v (h0 h1: HS.mem) (i: UInt64.t) (ll: LL1.t peer) (l: list peer): Lemma
  (requires
    LL1.well_formed h0 ll l /\
    LL1.invariant h0 ll l /\
    LL1.well_formed h1 ll l /\
    LL1.invariant h1 ll l /\
    LL1.cells h0 ll l == LL1.cells h1 ll l)
  (ensures (
    cell_by_id h0 i (LL1.cells h0 ll l) ==
    cell_by_id h1 i (LL1.cells h0 ll l)))
  (decreases l)
=
  // Crucially depends on same_cells_same_next.
  if B.g_is_null ll then
    ()
  else
    cell_by_id_depends_only_on_v h0 h1 i (B.deref h1 ll).LL1.next (List.Tot.tl l)
#pop-options

val insert_peer (d: device) (id: UInt64.t) (hs: handshake_state): ST unit
  (requires fun h0 ->
    invariant h0 d /\
    peer_by_id id (LL2.v h0 d.peers) == None /\

    B.live h0 hs /\
    B.length hs == 8 /\
    B.freeable hs /\
    B.loc_addr_of_buffer hs `B.loc_disjoint` peers_footprint (LL2.v h0 d.peers) /\
    B.(loc_all_regions_from false d.r_peers_payload `loc_includes` loc_addr_of_buffer hs)
    )
  (ensures fun h0 _ h1 ->
    invariant h1 d /\ (
    let peers = LL2.v h1 d.peers in
    Cons? peers /\ (
    let p :: ps = peers in
    p.id == id /\
    p.hs == hs /\
    ps == LL2.v h0 d.peers /\
    // Clients can conclude that hs remains unchanged.
    B.(modifies (loc_all_regions_from false d.r_peers) h0 h1))))

/// Because of this using_facts_from I have to manually call
/// loc_unused_in_not_unused_in_disjoint after every stateful operation.
#push-options "--z3rlimit 200 --fuel 1 \
  --using_facts_from '* -LowStar.Monotonic.Buffer.unused_in_not_unused_in_disjoint_2'"
let insert_peer d id hs =
  (**) let h0 = ST.get () in
  (**) B.loc_unused_in_not_unused_in_disjoint h0;
  (**) let l0: G.erased _ = LL2.v h0 d.peers in

  let device = B.malloc d.r_peers_payload d 1ul in
  (**) let h01 = ST.get () in
  (**) B.loc_unused_in_not_unused_in_disjoint h01;

  let p = { id; hs; device } in
  LL2.push d.peers p;
  // Let's start by stating some things we know
  (**) let h1 = ST.get () in
  (**) let l1: G.erased _ = LL2.v h1 d.peers in
  (**) B.loc_unused_in_not_unused_in_disjoint h1;
  (**) assert B.(modifies (loc_all_regions_from false d.r_peers) h0 h1);

  //(**) push_grows_footprint d.peers h0 h1;
  // This one does not trigger...
  (**) LL2.footprint_in_r h1 d.peers;

  // Establishing IM.invariant
  (**) IM.frame d.peer_of_id (B.loc_all_regions_from false d.r_peers) h0 h1;
  (**) assert (IM.v h1 d.peer_of_id == IM.v h0 d.peer_of_id);

  // This one crucially relies on the loc_in clause. Note: I tried to keep the
  // loc_in in the invariant but this turned out to be a nightmare to establish
  // (cf a discussion with Tahina on address-insensitive locations to which I
  // understand close to nothing), so it's easier to derive it from the
  // invariant. In general, there's a limit to how much stuff one should cram
  // into the invariant!
  (**) peer_footprint_in h0 d.r_peers_payload (LL2.v h0 d.peers);
  (**) assert (peers_disjoint (LL2.v h1 d.peers));

  // Trying to establish peers_invariant
  (**) assert (peer_invariant h1 p);
  (**) assert (B.(loc_all_regions_from false d.r_peers_payload `loc_includes` peer_footprint p));
  (**) assert (peers_invariants h0 d.r_peers_payload (LL2.v h0 d.peers));
  (**) frame_peers_invariants d.r_peers_payload (B.deref h0 d.peers.LL2.ptr) (B.deref h0 d.peers.LL2.v)
    B.(loc_all_regions_from false d.r_peers) h0 h1;
  (**) assert (peers_invariants h1 d.r_peers_payload (LL2.v h0 d.peers));
  (**) assert (peers_invariants h1 d.r_peers_payload (LL2.v h1 d.peers));

  // Now, peers_back... getting near the end of the global invariant.
  (**) frame_peers_back B.(loc_all_regions_from false d.r_peers) h0 h1 d (LL2.v h0 d.peers);

  // Last part of the invariant. Note: this is littered with asserts, most of
  // which aren't strictly necessary for the proof, but while debugging the
  // invariant and establishing auxiliary lemmas (e.g. same_pointer_same_thing)
  // they were really helpful, so I'm leaving them in.
  let aux (i: UInt64.t): Lemma
    (ensures (peer_of_id_in_peers h1 d i))
    [ SMTPat (peer_of_id_in_peers h1 d i) ]
  =
    assert (peer_of_id_in_peers h0 d i);
    assert (IM.v h1 d.peer_of_id == IM.v h0 d.peer_of_id);
    cell_by_id_is_peer_by_id h1 i (B.deref h1 d.peers.LL2.ptr) (B.deref h1 d.peers.LL2.v);
    cell_by_id_is_peer_by_id h0 i (B.deref h0 d.peers.LL2.ptr) (B.deref h0 d.peers.LL2.v);
    if i = id then begin
      if Some? (M.sel (IM.v h0 d.peer_of_id) i) then begin
        assert (Some? (peer_by_id i (LL2.v h0 d.peers)));
        false_elim ()
      end;
      let _ = allow_inversion (option (LL1.t peer)) in
      assert (M.sel (IM.v h0 d.peer_of_id) i == None);
      assert (M.sel (IM.v h1 d.peer_of_id) i == None);
      ()
    end else begin
      // Some reasoning about v peer_by_id... easy because it's not a stateful predicate.
      assert (peer_by_id i (LL2.v h1 d.peers) == peer_by_id i (List.Tot.tl (LL2.v h1 d.peers)));
      assert (peer_by_id i (LL2.v h1 d.peers) == peer_by_id i (LL2.v h0 d.peers));
      // The cell is to be found in the tail of the list.
      assert ((B.deref h1 (List.Tot.hd (LL2.cells h1 d.peers))).LL1.data == p);
      assert (cell_by_id h1 i (LL2.cells h1 d.peers) == cell_by_id h1 i (List.Tot.tl (LL2.cells h1 d.peers)));
      assert (cell_by_id h1 i (LL2.cells h1 d.peers) == cell_by_id h1 i (LL2.cells h0 d.peers));
      assert (LL2.cells h0 d.peers == LL1.cells h0 (B.deref h0 d.peers.LL2.ptr) (B.deref h0 d.peers.LL2.v));
      assert (List.Tot.tl (LL2.cells h1 d.peers) == LL1.cells h0 (B.deref h0 d.peers.LL2.ptr) (B.deref h0 d.peers.LL2.v));
      assert (LL1.well_formed h0 (B.deref h0 d.peers.LL2.ptr) (B.deref h0 d.peers.LL2.v));
      assert (LL1.well_formed h1 (B.deref h1 d.peers.LL2.ptr) (B.deref h1 d.peers.LL2.v));
      let _ = allow_inversion (list peer) in
      assert LL1.(well_formed h1 (B.deref h1 (B.deref h1 d.peers.LL2.ptr)).next (List.Tot.tl (B.deref h1 d.peers.LL2.v)));
      assert (List.Tot.tl (B.deref h1 d.peers.LL2.v) == LL2.v h0 d.peers);
      // Also crucially depends on same_cells_same_pointer.
      cell_by_id_depends_only_on_v h0 h1 i (B.deref h0 d.peers.LL2.ptr) (LL2.v h0 d.peers)
      end
  in
  ()

/// Continuing with the convention that the _ suffix indicates a function that
/// operates on a LL1 and that a more convenient function is about to follow.
/// Note that this function is specified in terms of cell_by_id which is
/// stronger and can be converted to peer_by_id via the suitable lemma.
let rec find_peer_by_id_ (ll: LL1.t peer) (l: G.erased (list peer)) (id: UInt64.t):
  Stack (B.pointer_or_null (LL1.cell peer))
    (requires fun h0 ->
      LL1.well_formed h0 ll l /\
      LL1.invariant h0 ll l)
    (ensures fun h0 p h1 ->
      h0 == h1 /\ (
      let maybe_cell = cell_by_id h0 id (LL1.cells h0 ll l) in
      (None? maybe_cell <==> B.g_is_null p) /\ (
      not (B.g_is_null p) ==>
        Some?.v maybe_cell == p)))
=
  let _ = allow_inversion (list peer) in
  if B.is_null ll then
    B.null
  else
    let { LL1.next; LL1.data } = !* ll in
    if data.id = id then
      ll
    else
      find_peer_by_id_ next (List.Tot.tl l) id

let find_peer_by_id (d: device) (id: UInt64.t):
  Stack (B.pointer_or_null (LL1.cell peer))
    (requires fun h0 ->
      invariant h0 d)
    (ensures fun h0 p h1 ->
      h0 == h1 /\ (
      let maybe_cell = cell_by_id h0 id (LL2.cells h0 d.peers) in
      (None? maybe_cell <==> B.g_is_null p) /\ (
      not (B.g_is_null p) ==>
        Some?.v maybe_cell == p)))
=
  find_peer_by_id_ !*d.peers.LL2.ptr !*d.peers.LL2.v id

let link_peer_by_id (d: device) (id: UInt64.t):
  Stack unit
    (requires fun h0 ->
      invariant h0 d /\
      Some? (peer_by_id id (LL2.v h0 d.peers)))
    (ensures fun h0 _ h1 ->
      B.(modifies (loc_all_regions_from false d.r_peer_of_id) h0 h1) /\
      invariant h1 d /\
      Some? (M.sel (IM.v h1 d.peer_of_id) id))
=
  admit ()

let main (): St Int32.t =
  let r = ST.new_region HS.root in
  let m: IM.t nat (nat & nat) = IM.create_in r in
  (**) let h0 = ST.get () in
  (**) assert (M.sel (IM.v h0 m) 0 == None);
  IM.add m 0 (1, 2);
  (**) let h1 = ST.get () in
  (**) assert (M.sel (IM.v h1 m) 0 == Some (1, 2));
  let b = B.malloc HS.root 0ul 1ul in
  (**) let h2 = ST.get () in
  (**) assert (M.sel (IM.v h2 m) 0 == Some (1, 2));
  b *= 2ul;
  (**) let h3 = ST.get () in
  (**) assert (M.sel (IM.v h3 m) 0 == Some (1, 2));
  IM.add m 0 (2, 1);
  (**) let h4 = ST.get () in
  (**) assert (M.sel (IM.v h4 m) 0 == Some (2, 1));
  (**) assert (B.deref h4 b == 2ul);
  IM.remove_all m 1;
  (**) let h5 = ST.get () in
  (**) assert (M.sel (IM.v h5 m) 0 == Some (2, 1));
  (**) assert (B.deref h5 b == 2ul);
  IM.remove_all m 0;
  (**) let h6 = ST.get () in
  (**) assert (M.sel (IM.v h6 m) 0 == None);
  (**) assert (B.deref h6 b == 2ul);
  0l
