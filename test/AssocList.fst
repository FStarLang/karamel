module AssocList

/// Testing the API of the interactive map

module I = LowStar.Lib.AssocList
module M = FStar.Map
module B = LowStar.Buffer
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module LL1 = LowStar.Lib.LinkedList
module LL2 = LowStar.Lib.LinkedList2

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
  peer_of_id: I.t UInt64.t (LL1.t peer);
  r: HS.rid;
  r_peers: HS.rid;
  r_peer_of_id: HS.rid;
  r_handshake: HS.rid;
}

/// A single peer
/// -------------
let peer_invariant (h: HS.mem) (p: peer) =
  B.live h p.hs /\ B.length p.hs == 8 /\
  B.freeable p.hs

let peer_footprint (h: HS.mem) (p: peer) =
  B.loc_addr_of_buffer p.hs

/// Properties of the payload of the linked list
/// --------------------------------------------

// Cannot use List.Tot.fold_right because GTot / Tot effect mistmatch
let rec peers_footprint (h: HS.mem) (ps: list peer): GTot B.loc =
  allow_inversion (list peer);
  match ps with
  | [] -> B.loc_none
  | p :: ps -> peer_footprint h p `B.loc_union` peers_footprint h ps

let rec peers_disjoint (h: HS.mem) (ps: list peer) =
  allow_inversion (list peer);
  match ps with
  | [] -> True
  | p :: ps ->
      peer_footprint h p `B.loc_disjoint` peers_footprint h ps /\
      peers_disjoint h ps

let rec peers_invariant (h: HS.mem) (r: HS.rid) (ps: list peer) =
  allow_inversion (list peer);
  match ps with
  | [] -> True
  | p :: ps ->
      B.(loc_region_only false r `loc_includes` peer_footprint h p) /\
      peer_invariant h p /\
      peers_disjoint h ps /\
      peers_invariant h r ps

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

let peer_of_id_in_peers (h: HS.mem) (d: device) (i: UInt64.t) =
  let m = I.v h d.peer_of_id in
  let p = peer_by_id i (LL2.v h d.peers) in
  match M.sel m i with
  | None -> p == None
  | Some ptr ->
      ~(B.g_is_null ptr) /\
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
  ST.is_eternal_region d.r_handshake /\

  HS.extends d.r_peers d.r /\
  HS.extends d.r_peer_of_id d.r /\
  HS.extends d.r_handshake d.r /\

  HS.parent d.r_peers == d.r /\
  HS.parent d.r_peer_of_id == d.r /\
  HS.parent d.r_handshake == d.r /\

  B.(loc_disjoint (loc_region_only false d.r_peers) (loc_region_only false d.r_peer_of_id)) /\
  B.(loc_disjoint (loc_region_only false d.r_peers) (loc_region_only false d.r_handshake)) /\
  B.(loc_disjoint (loc_region_only false d.r_peer_of_id) (loc_region_only false d.r_handshake)) /\

  d.peers.LL2.r == d.r_peers /\
  I.region_of d.peer_of_id == B.loc_all_regions_from false d.r_peer_of_id /\
  // This is covered by the peers_invariant:
  // loc_region d.r_handshake `loc_includes` peers_footprint (LL2.v h d.peers)

  (forall (i: UInt64.t). {:pattern peer_of_id_in_peers h d i }
    peer_of_id_in_peers h d i) /\
  peers_back h d (LL2.v h d.peers) /\

  LL2.invariant h d.peers /\
  I.invariant h d.peer_of_id

#push-options "--fuel 1"
let create_in (r: HS.rid): ST device
  (requires fun h0 ->
    ST.is_eternal_region r)
  (ensures fun h0 d h1 ->
    invariant h1 d /\
    B.(modifies loc_none h0 h1) /\
    I.v h1 d.peer_of_id == M.const None /\
    LL2.v h1 d.peers == [] /\
    d.r == r)
=
  let r_peers = ST.new_region r in
  let r_peer_of_id = ST.new_region r in
  let r_handshake = ST.new_region r in
  let peers = LL2.create_in r_peers in
  let peer_of_id = I.create_in r_peer_of_id in
  { peers; peer_of_id; r; r_peers; r_peer_of_id; r_handshake }
#pop-options

let test (): St unit =
  let r = ST.new_region HS.root in
  let d = create_in r in
  // TODO: talk about where the backpoint lives (which region?), how live it is, etc. etc. etc.
  let p = { id = 0UL; hs = B.malloc d.r_handshake 0uy 8ul; device = B.malloc HS.root d 1ul } in
  LL2.push d.peers p;
  let h1 = ST.get () in
  () // assert (invariant h1 d)

let main (): St Int32.t =
  let r = ST.new_region HS.root in
  let m: I.t nat (nat & nat) = I.create_in r in
  (**) let h0 = ST.get () in
  (**) assert (M.sel (I.v h0 m) 0 == None);
  I.add m 0 (1, 2);
  (**) let h1 = ST.get () in
  (**) assert (M.sel (I.v h1 m) 0 == Some (1, 2));
  let b = B.malloc HS.root 0ul 1ul in
  (**) let h2 = ST.get () in
  (**) assert (M.sel (I.v h2 m) 0 == Some (1, 2));
  b *= 2ul;
  (**) let h3 = ST.get () in
  (**) assert (M.sel (I.v h3 m) 0 == Some (1, 2));
  I.add m 0 (2, 1);
  (**) let h4 = ST.get () in
  (**) assert (M.sel (I.v h4 m) 0 == Some (2, 1));
  (**) assert (B.deref h4 b == 2ul);
  I.remove_all m 1;
  (**) let h5 = ST.get () in
  (**) assert (M.sel (I.v h5 m) 0 == Some (2, 1));
  (**) assert (B.deref h5 b == 2ul);
  I.remove_all m 0;
  (**) let h6 = ST.get () in
  (**) assert (M.sel (I.v h6 m) 0 == None);
  (**) assert (B.deref h6 b == 2ul);
  0l
