module FunctionalUpdate

module B = LowStar.Buffer
open LowStar.BufferOps
open FStar.HyperStack.ST

type point = {
  x: (x:Int32.t { 0 <= Int32.v x && Int32.v x <= 2 });
  y: (y:Int32.t { 0 <= Int32.v y && Int32.v y <= 2 });
}

type point3d = {
  x: (x:Int32.t { 0 <= Int32.v x && Int32.v x <= 2 });
  y: (y:Int32.t { 0 <= Int32.v y && Int32.v y <= 2 });
  z: (z:Int32.t { 0 <= Int32.v z && Int32.v z <= 2 });
}

noeq type point_indir = { point_ref : B.pointer point3d; other : Int32.t }

let f1 (p: B.buffer point): Stack unit
  (requires (fun h -> B.live h p /\ B.length p = 1))
  (ensures (fun _ _ _ -> True))
=
  let open LowStar.BufferOps in
  p.(0ul) <- ({ p.(0ul) with x = 0l })

let g1 (p: B.buffer point): Stack unit
  (requires (fun h -> B.live h p /\ B.length p = 1))
  (ensures (fun _ _ _ -> True))
=
  let open LowStar.BufferOps in
  p *= ({ !*p with y = 0l })

let f2 (p: B.buffer point3d): Stack unit
  (requires (fun h -> B.live h p /\ B.length p = 1))
  (ensures (fun _ _ _ -> True))
=
  let open LowStar.BufferOps in
  p.(0ul) <- ({ p.(0ul) with x = 0l })

let g2 (p: B.buffer point3d): Stack unit
  (requires (fun h -> B.live h p /\ B.length p = 1))
  (ensures (fun _ _ _ -> True))
=
  let open LowStar.BufferOps in
  p *= ({ !*p with y = 0l })

let test_set_field2 (r: point_indir)
  : Stack unit (requires fun h -> B.live h r.point_ref) (ensures fun _ _ _ -> True)
  =
    r.point_ref.(0ul) <- { r.point_ref.(0ul) with z = 0l }

let main (): St Int32.t =
  push_frame ();
  let r1 = B.alloca (({ x = 1l; y = 2l } <: point)) 1ul in
  f1 r1;
  g1 r1;
  let r2: B.buffer point3d = B.alloca ({ x = 1l; y = 2l; z = 2l }) 1ul in
  f2 r2;
  g2 r2;
  test_set_field2 ({ point_ref = r2; other = 0l });
  let ret = (!*r1).x `Int32.add` (!*r1).y `Int32.add` (!*r2).x `Int32.add` (!*r2).y `Int32.add` (!*r2).z in
  pop_frame ();
  ret
