module Polymorphic

open FStar.HyperStack.ST

let id #a (x: a): Stack a (fun _ -> true) (fun _ _ _ -> true) =
  x

let id1 (x: FStar.UInt32.t): Stack FStar.UInt32.t (fun _ -> true) (fun _ _ _ -> true) =
  id x

let id2 (x: FStar.UInt64.t): Stack FStar.UInt64.t (fun _ -> true) (fun _ _ _ -> true) =
  id x

let main (): Stack FStar.Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  TestLib.checku32 (id1 0ul) 0ul;
  TestLib.checku64 (id2 0UL) 0UL;
  0l
