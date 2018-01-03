module MutRec

open FStar.HyperStack.ST
open FStar.Buffer

module B = FStar.Buffer

let rec f (): StackInline (B.buffer Int32.t) (fun _ -> true) (fun _ x h -> B.live h x /\ B.length x = 1) =
  B.createL [ 0l ]

and g (): Stack Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  push_frame ();
  let b = f () in
  let r = b.(0ul) in
  pop_frame ();
  r

let main (): Stack Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  g ()
