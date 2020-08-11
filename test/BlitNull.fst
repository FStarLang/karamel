module BlitNull

let main () : FStar.HyperStack.ST.Stack Int32.t (fun _ -> True) (fun _ _ _ -> True) =
  LowStar.Buffer.(blit #bool null 0ul null 0ul 0ul);
  0l
