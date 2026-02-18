module DeclOrder

open FStar.HyperStack.ST
module U32 = FStar.UInt32

(* This test exercises the declaration ordering fix for non-polymorphic
   types. The polymorphic wrapper 'box' triggers monomorphisation.
   Type 'outer' uses box<inner> by value, so inner must be emitted
   before the monomorphised box<inner>, which must be emitted before
   outer. Without the DFS-ordering fix (commits d72e7fa0 and c105d056),
   non-polymorphic types like 'inner' were deferred to source position,
   appearing after the types that embed them by value. *)

noeq
type box ([@@@strictly_positive] a: Type0) = {
  value: a;
  tag: U32.t
}

noeq
type outer = {
  wrapped: box inner;
  extra: U32.t
}

and inner = {
  x: U32.t;
  y: U32.t
}

let make_inner (): inner =
  { x = 1ul; y = 2ul }

let make_outer (): outer =
  { wrapped = { value = make_inner (); tag = 0ul }; extra = 42ul }

let main () =
  let o = make_outer () in
  if o.extra = 42ul then 0l else 1l



