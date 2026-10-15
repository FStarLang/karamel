module C89RecordInlining

module B = LowStar.Buffer
module HST = FStar.HyperStack.ST

type counters = { first: UInt32.t; second: UInt32.t; tag: UInt32.t }
type nested = { inner: counters; keep: UInt32.t }

(* C89 lowers record literals to uninitialized storage followed by field
   assignments. Aggressive inlining must retain that storage. *)
let update (p: B.pointer counters) (value: UInt32.t): HST.Stack UInt32.t
  (fun h -> B.live h p)
  (fun _ _ _ -> True)
= let old = B.index p 0ul in
  B.upd p 0ul { old with first = value };
  old.first

let swap (p: B.pointer counters): HST.Stack unit
  (fun h -> B.live h p)
  (fun _ _ _ -> True)
= let old = B.index p 0ul in
  B.upd p 0ul { old with first = old.second; second = old.first }

let update_nested (p: B.pointer nested): HST.Stack unit
  (fun h -> B.live h p)
  (fun _ _ _ -> True)
= let old = B.index p 0ul in
  B.upd p 0ul { old with inner = { old.inner with first = 42ul } }

let main (): HST.Stack Int32.t
  (fun _ -> True)
  (fun _ _ _ -> True)
= HST.push_frame ();
  let p = B.alloca { first = 11ul; second = 22ul; tag = 17ul } 1ul in
  let before = update p 99ul in
  swap p;
  let result = B.index p 0ul in
  let q = B.alloca { inner = result; keep = 33ul } 1ul in
  update_nested q;
  let nested_result = B.index q 0ul in
  let ok = before = 11ul && result.first = 22ul && result.second = 99ul &&
    result.tag = 17ul && nested_result.inner.first = 42ul &&
    nested_result.inner.second = 99ul && nested_result.inner.tag = 17ul &&
    nested_result.keep = 33ul in
  HST.pop_frame ();
  if ok then 0l else 1l
