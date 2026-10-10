module FunctionalUpdates

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST

type counters = { first: UInt32.t; second: UInt32.t; untouched: UInt32.t }

let swap_snapshot (p: B.buffer counters): ST.Stack unit
  (requires (fun h -> B.live h p /\ B.length p == 1))
  (ensures (fun _ _ _ -> True))
=
  let old = B.index p 0ul in
  B.upd p 0ul { old with first = old.second; second = old.first }

let swap_and_return_old (p: B.buffer counters): ST.Stack UInt32.t
  (requires (fun h -> B.live h p /\ B.length p == 1))
  (ensures (fun _ _ _ -> True))
=
  let old = B.index p 0ul in
  B.upd p 0ul { old with first = old.second; second = old.first };
  old.first

let swap_fields (p: B.buffer counters): ST.Stack unit
  (requires (fun h -> B.live h p /\ B.length p == 1))
  (ensures (fun _ _ _ -> True))
=
  let first = (B.index p 0ul).first in
  let second = (B.index p 0ul).second in
  B.upd p 0ul { first = second; second = first;
               untouched = (B.index p 0ul).untouched }

let set_and_return_old (p: B.buffer counters) (value: UInt32.t): ST.Stack UInt32.t
  (requires (fun h -> B.live h p /\ B.length p == 1))
  (ensures (fun _ _ _ -> True))
=
  let old = B.index p 0ul in
  B.upd p 0ul { old with first = value };
  old.first

let set_and_return_arg (p: B.buffer counters) (value result: UInt32.t): ST.Stack UInt32.t
  (requires (fun h -> B.live h p /\ B.length p == 1))
  (ensures (fun _ _ _ -> True))
=
  let old = B.index p 0ul in
  B.upd p 0ul { old with first = value };
  result

let set_at_index (p: B.buffer counters) (i: UInt32.t) (value: UInt32.t): ST.Stack unit
  (requires (fun h -> B.live h p /\ UInt32.v i < B.length p))
  (ensures (fun _ _ _ -> True))
=
  let old = B.index p i in
  B.upd p i { old with first = value }

(* Once field updates leave only one use of old, CInline lets optimize_lets
   turn this into p->first = p->second. *)
let clobber (p: B.buffer counters): ST.Stack unit
  (requires (fun h -> B.live h p /\ B.length p == 1))
  (ensures (fun _ _ _ -> True))
=
  [@@CInline] let old = B.index p 0ul in
  B.upd p 0ul { old with first = old.second }

(* While it may look that this could become p->first = f(),
   the call to f could modify the contents of p (if effectful, and it gets
   some way to access p). This testcase is here since I initially thought
   we could use functional updates for impure values in the case where
   only a single field is updated, but no. *)
let not_even_with_a_single_field (p: B.buffer counters)
  (f : unit -> UInt32.t)
: ST.Stack unit
  (requires (fun h -> B.live h p /\ B.length p == 1))
  (ensures (fun _ _ _ -> True))
=
  let old = B.index p 0ul in
  B.upd p 0ul { old with first = f () }
