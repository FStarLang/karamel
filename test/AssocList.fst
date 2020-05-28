module AssocList

/// Testing the API of the interactive map

module I = LowStar.Lib.AssocList
module M = FStar.Map
module B = LowStar.Buffer
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

open LowStar.BufferOps
open FStar.HyperStack.ST

#set-options "--fuel 0 --ifuel 0"

let main (): St unit =
  let r = ST.new_region HS.root in
  let m: I.t nat (nat & nat) = I.create_in r in
  (**) let h0 = ST.get () in
  (**) assert (M.sel (I.v h0 m) 0 == None);
  I.add m 0 (1, 2);
  (**) let h1 = ST.get () in
  (**) assert (M.sel (I.v h1 m) 0 == Some (1, 2));
  let b = B.malloc HS.root 0ul 1ul in
  (**) let h2 = ST.get () in
  I.frame m B.loc_none h1 h2;
  (**) assert (M.sel (I.v h2 m) 0 == Some (1, 2));
  b *= 2ul;
  b *= 2ul; // UNCOMMENT THIS TO TRIGGER THE BUG
  (**) let h3 = ST.get () in
  I.frame m (B.loc_buffer b) h2 h3;
  I.footprint_in_r h3 m;
  (**) assert B.(loc_disjoint (loc_buffer b) (I.footprint h3 m));
  (**) assert (M.sel (I.v h3 m) 0 == Some (1, 2));
  (**) assert B.(deref h3 b == 2ul); // UNCOMMENT THIS TO TRIGGER THE BUG IN A DIFFERENT LOCATION
  I.add m 0 (2, 1);
  (**) let h4 = ST.get () in
  (**) assert (M.sel (I.v h4 m) 0 == Some (2, 1));
  (**) assert (B.deref h4 b == 2ul);
  I.footprint_in_r h4 m;
  (**) assert B.(loc_disjoint (loc_buffer b) (I.footprint h4 m));
  I.remove_all m 1;
  (**) let h5 = ST.get () in
  (**) assert (M.sel (I.v h5 m) 0 == Some (2, 1));
  (**) assert (B.deref h5 b == 2ul);
  I.footprint_in_r h5 m;
  I.remove_all m 0;
  (**) let h6 = ST.get () in
  (**) assert (M.sel (I.v h6 m) 0 == None);
  I.footprint_in_r h6 m;
  (**) assert (B.deref h6 b == 2ul);
  ()
