module PushPop

module HST = FStar.HyperStack.ST

let test (x: option unit) : HST.ST unit (requires (fun _ -> Some? x)) (ensures (fun _ _ _ -> True)) =
  HST.push_frame ();
  let (Some y) = x in
  HST.pop_frame ();
  y

let main (): HST.St Int32.t =
  test (Some ());
  0l
