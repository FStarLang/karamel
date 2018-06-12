module OldAndNew

module Old = FStar.Buffer
module OldM = FStar.Modifies
module New = LowStar.Buffer
module NewM = LowStar.Modifies
module HST = FStar.HyperStack.ST

open LowStar.ToFStarBuffer

/// Basic example of mutating a new buffer by converting it first to
/// an old buffer.
///
/// The spec shows that all three flavors of modifies clauses can be
/// proven and the precise contents are reflected into the new buffer
let ex1 (b:New.buffer FStar.UInt32.t {New.length b > 0}) (b1:New.buffer FStar.UInt32.t)
  : HST.Stack unit
           (requires (fun h -> New.live h b /\ New.disjoint b b1 /\ New.live h b1))
           (ensures (fun h0 _ h1 ->
             New.get h1 b 0 == 1729ul /\
             Old.get h1 (new_to_old_ghost b) 0 == 1729ul /\
             New.as_seq h0 b1 == New.as_seq h1 b1 /\
             NewM.modifies (NewM.loc_buffer b) h0 h1 /\
             OldM.modifies (OldM.loc_buffer (new_to_old_ghost b)) h0 h1 /\
             Old.modifies_1 (new_to_old_ghost b) h0 h1)) =
  let old = new_to_old_st b in
  Old.upd old 0ul 1729ul

let ex2 (b:New.buffer FStar.UInt32.t {New.length b > 0}) (b1:New.buffer FStar.UInt32.t)
  : HST.Stack unit
           (requires (fun h -> New.live h b /\ New.disjoint b b1 /\ New.live h b1))
           (ensures (fun h0 _ h1 ->
             New.get h1 b 0 == 1729ul /\
             New.as_seq h0 b1 == New.as_seq h1 b1 /\
             NewM.modifies (NewM.loc_buffer b) h0 h1)) =
  New.upd b 0ul 1729ul

let main () : HST.Stack FStar.Int32.t (requires (fun _ -> True)) (ensures (fun _ _ _ -> True)) =
  HST.push_frame ();
  let b1 = New.alloca 18ul 1ul in
  let b2 = New.alloca 42ul 1ul in
  ex1 b1 b2;
  ex2 b2 b1;
  HST.pop_frame ();
  0l
