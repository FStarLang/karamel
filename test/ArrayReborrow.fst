module ArrayReborrow

module B = LowStar.Buffer
module HST = FStar.HyperStack.ST

open ArrayReborrowData

let read (x: foo) : Int32.t = x.a

let deref () : HST.Stack Int32.t
  (fun h -> B.live h table /\ B.length table == 2)
  (fun _ _ _ -> True)
=
  let uu__x = B.index table C._zero_for_deref in
  read uu__x

let index () : HST.Stack Int32.t
  (fun h -> B.live h table /\ B.length table == 2)
  (fun _ _ _ -> True)
=
  let uu__x = B.index table 0ul in
  read uu__x

(* Used to generate read(&*p) instead of read p *)
let reborrow (p: B.buffer foo) : HST.Stack Int32.t
  (fun h -> B.live h p /\ B.length p > 0)
  (fun _ _ _ -> True)
=
  let uu__x = B.index p C._zero_for_deref in
  read uu__x
