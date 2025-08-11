module HigherOrder4

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module M = LowStar.Modifies
module I32 = FStar.Int32

open LowStar.BufferOps

/////////////////////////// Types ///////////////////////////
noeq type t_container (r:HS.rid) (t_Val:Type) =
| ContainerCons :
  vals     : (b:B.buffer t_Val  { (B.frameOf b) `HS.extends` r }) ->
  t_container r t_Val


inline_for_extraction
type t_EventHandler (a:Type) = (v:a) -> HST.Stack (unit)
  (requires (fun h -> True))
  (ensures (fun h0 x h1 -> True))

noeq type t_EventHandlerData (r:HS.rid) =
  | QueueAndHandler_Cons  :
    t_EventHandlerData r

/////////////////////////// Funcs ///////////////////////////

val dummyHandler : (#r:HS.rid) -> t_EventHandler (t_EventHandlerData r)
let dummyHandler #r _ = ()

let createContainer
  (t_Val:Type)
  (rContainer:HS.rid{HST.is_eternal_region rContainer})
  (initVal:t_Val)
  : HST.ST (t_container rContainer t_Val)
    (requires (fun h -> True))
    (ensures (fun h0 ret h1 -> B.live h1 ret.vals /\ M.modifies M.loc_none h0 h1))
=
  let rContainerSub = HST.new_region rContainer in
  let vals = B.malloc rContainerSub initVal 64ul in
  ContainerCons vals

let main(): HST.St I32.t =
  let rContainer = HST.new_region HS.root in
  let dict = (createContainer (t_EventHandler (t_EventHandlerData rContainer)) rContainer dummyHandler) in
  0l
