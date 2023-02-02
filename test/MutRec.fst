module MutRec

open FStar.HyperStack.ST
open FStar.Buffer

module B = FStar.Buffer

private
let rec f (): StackInline (B.buffer Int32.t) (fun _ -> true) (fun _ x h -> B.live h x /\ B.length x = 1) =
  B.createL [ 0l ]


and g (): Stack Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  push_frame ();
  let b = f () in
  let r = b.(0ul) in
  pop_frame ();
  r

private let rec f1 (i: Int32.t { Int32.v i >= 0 }): Stack Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  if i = 0l then
    i
  else
    g1 (i `FStar.Int32.sub` 1l)

and g1 (i: Int32.t{ Int32.v i >= 0 }): Stack Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  if i = 0l then
    i
  else
    f1 (i `FStar.Int32.sub` 1l)

let main (): Stack Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  let x = g () in
  let y = g1 1l in
  if x = 0l && y = 0l then
    0l
  else
    1l
