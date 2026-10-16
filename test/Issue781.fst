module Issue781

(* Partial application of a local function. Inlining this used to leave an
   out-of-scope variable. It must now report the unsupported partial application. *)
let f (p:FStar.UInt32.t) : unit -> FStar.UInt32.t =
  let g (a:unit) (b:unit) = p in
  g ()
