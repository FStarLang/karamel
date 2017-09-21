module C89

open FStar.HyperStack.ST
open FStar.HyperStack

let f (): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  ()

let g (): Stack Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  0l

let h (x y: Int32.t): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  ()

let i (): Stack UInt32.t (fun _ -> true) (fun _ _ _ -> true) =
  0ul

let j (): Stack (UInt32.t * UInt32.t) (fun _ -> true) (fun _ _ _ -> true) =
  1ul, 2ul

let main (): Stack Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  push_frame ();
  f ();
  let x = g () in
  h (g ()) (g ());
  let y = g () in
  let b = Buffer.create (i ()) 32ul in
  h x y;
  let _ = j () in
  pop_frame ();
  0l
