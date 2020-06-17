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
  r_peers: HS.rid;
  r_peer_of_id: HS.rid;
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

let peer_of_id_in_peers (h: HS.mem) (d: device) (i: UInt64.t): Ghost Type
  (requires LL2.invariant h d.peers)
  (ensures fun _ -> True)
=
  let m = IM.v h d.peer_of_id in
  let p = peer_by_id i (LL2.v h d.peers) in
  match M.sel m i with
  | None -> p == None
  | Some ptr ->
      ~(B.g_is_null ptr) /\
      B.(loc_includes (LL2.footprint h d.peers) (loc_addr_of_buffer ptr)) /\
      p == Some ((B.deref h ptr).LL1.data)

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
  // Technicality: just like for LL1 (see comment there), since the footprint of
  // the payload of the peers is recursive, we don't automatically get
  // disjointness of fresh allocations w.r.t. peers_footprint which is a drag.
  B.loc_in (peers_footprint (LL2.v h d.peers)) h /\

  (forall (i: UInt64.t). {:pattern peer_of_id_in_peers h d i }
    peer_of_id_in_peers h d i) /\
  peers_back h d (LL2.v h d.peers)


#push-options "--fuel 1 --ifuel 1"
let rec frame_peers_invariant (r_payload: HS.rid) (l: LL1.t peer) (n: list peer) (r: B.loc) (h0 h1: HS.mem): Lemma
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
  [ SMTPat (peers_invariant h1 r_payload n); SMTPat (LL1.well_formed h1 l n); SMTPat (B.modifies r h0 h1) ]
=
  if B.g_is_null l then
    ()
  else
    let p = List.Tot.hd n in
    let ps = List.Tot.tl n in
    frame_peers_invariant r_payload (B.deref h0 l).LL1.next (List.Tot.tl n) r h0 h1
#pop-options

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
    frame_peers_invariant r_peers_payload next (List.Tot.tl l)
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


#push-options "--ifuel 1"
let rec footprint_via_cells #a (l: list (B.pointer (LL1.cell a))): GTot B.loc =
  match l with
  | c :: cs -> B.loc_addr_of_buffer c `B.loc_union` footprint_via_cells cs
  | [] -> B.loc_none
#pop-options

#push-options "--fuel 1 --ifuel 1"
let rec footprint_via_cells_is_footprint #a (h: HS.mem) (ll: LL1.t a) (l: list a): Lemma
  (requires LL1.well_formed h ll l)
  (ensures
    LL1.footprint h ll l == footprint_via_cells (LL1.cells h ll l))
  (decreases l)
=
  if B.g_is_null ll then
    ()
  else
    footprint_via_cells_is_footprint h (B.deref h ll).LL1.next (List.Tot.tl l)
#pop-options

#push-options "--fuel 1 --ifuel 1"
let push_grows_footprint #a (ll: LL2.t a) (h0 h1: HS.mem): Lemma
  (requires (
    LL2.invariant h0 ll /\
    LL2.invariant h1 ll /\
    Cons? (LL2.cells h1 ll) /\
    List.Tot.tl (LL2.cells h1 ll) == LL2.cells h0 ll /\
    List.Tot.tl (LL2.v h1 ll) == LL2.v h0 ll))
  (ensures (
    LL2.footprint h1 ll `B.loc_includes` LL2.footprint h0 ll))
=
  let open LL2 in
  let head = B.deref h1 ll.ptr in
  let v = B.deref h1 ll.v in
  calc (==) {
    footprint h1 ll;
  (==) { }
    B.(loc_addr_of_buffer ll.ptr `loc_union`
      loc_addr_of_buffer ll.v `loc_union` LL1.footprint h1 head v);
  (==) { }
    B.(loc_addr_of_buffer ll.ptr `loc_union`
      loc_addr_of_buffer ll.v `loc_union`
      (loc_addr_of_buffer (B.deref h1 ll.ptr) `loc_union`
      LL1.footprint h1 (B.deref h1 head).LL1.next (List.Tot.tl v)));
  (==) { footprint_via_cells_is_footprint h1 (B.deref h1 head).LL1.next (List.Tot.tl v) }
    B.(loc_addr_of_buffer ll.ptr `loc_union`
      loc_addr_of_buffer ll.v `loc_union`
      (loc_addr_of_buffer (B.deref h1 ll.ptr) `loc_union`
      footprint_via_cells (LL1.cells h1 (B.deref h1 head).LL1.next (List.Tot.tl v))));
  (==) { }
    B.(loc_addr_of_buffer ll.ptr `loc_union`
      loc_addr_of_buffer ll.v `loc_union`
      (loc_addr_of_buffer (B.deref h1 ll.ptr) `loc_union`
      footprint_via_cells (LL2.cells h0 ll)));
  (==) { footprint_via_cells_is_footprint h0 (B.deref h0 ll.LL2.ptr) (List.Tot.tl v) }
    B.(loc_addr_of_buffer ll.ptr `loc_union`
      loc_addr_of_buffer ll.v `loc_union`
      (loc_addr_of_buffer (B.deref h1 ll.ptr) `loc_union`
      LL1.footprint h0 (B.deref h0 ll.ptr) (List.Tot.tl v)));
  }
#pop-options

val insert_peer (d: device) (id: UInt64.t) (hs: handshake_state): ST unit
  (requires fun h0 ->
    invariant h0 d /\
    peer_by_id id (LL2.v h0 d.peers) == None /\

    B.live h0 hs /\
    B.length hs == 8 /\
    B.freeable hs /\
    // TODO: probably need to keep a loc_in peers_footprint in the global invariant
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

#push-options "--z3rlimit 100 --ifuel 1 --fuel 1"
let insert_peer d id hs =
  (**) let h0 = ST.get () in
  (**) let l0: G.erased _ = LL2.v h0 d.peers in
  let device = B.malloc d.r_peers_payload d 1ul in
  let p = { id; hs; device } in
  LL2.push d.peers p;
  (**) let h1 = ST.get () in
  (**) push_grows_footprint d.peers h0 h1;
  (**) let l1: G.erased _ = LL2.v h1 d.peers in
  (**) LL2.footprint_in_r h1 d.peers;
  (**) IM.frame d.peer_of_id (B.loc_all_regions_from false d.r_peers) h0 h1;
  (**) assert (IM.v h1 d.peer_of_id == IM.v h0 d.peer_of_id);
  (**) assert (peers_disjoint (LL2.v h1 d.peers));
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
