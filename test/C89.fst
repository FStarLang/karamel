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

let touch #a (x: a): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  ()

type t =
| A: Int32.t -> t
| B: Int64.t -> t

type point =
| Point2d: Int32.t -> Int32.t -> point
| Point3d: Int32.t -> Int32.t -> Int32.t -> point

(* let j (): Stack (UInt32.t * UInt32.t) (fun _ -> true) (fun _ _ _ -> true) = *)
(*   1ul, 2ul *)

let main (): Stack Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  push_frame ();
  f ();
  let x = g () in
  h (g ()) (g ());
  let y = g () in
  let b = Buffer.create (i ()) 32ul in
  let b' = Buffer.createL [ 0ul; 32ul ] in
  h x y;
  (* let _ = j () in *)
  touch (A 0l);
  let p = Point3d 0l 1l 2l in
  touch p;
  pop_frame ();
  0l
