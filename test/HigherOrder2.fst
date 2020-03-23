module HigherOrder2

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module I32 = FStar.Int32
module M = LowStar.Modifies
module U32 = FStar.UInt32


(* A function type we will use *)
inline_for_extraction type t_Func (t_Param:Type)  = 
  e:t_Param -> HST.Stack (unit)
    (requires (fun h -> True))
    (ensures (fun h0 ret h1 -> M.modifies (M.loc_none) h0 h1))

(* A type that holds a function pointer and a parameter *)
noeq type t_Closure (t_Param:Type) =
  | Closure_Cons :
    func     : t_Func t_Param ->
    param    : t_Param ->
    t_Closure t_Param

(* A function that invokes the target closure *)
val invoke (#t_Param:Type) (q:t_Closure t_Param) : HST.Stack (unit)
  (requires (fun h -> True))
  (ensures (fun h0 ret h1 -> (M.modifies M.loc_none h0 h1)))
let invoke #t_Param q =
  // JP: this is seen as the following application:
  // proj_func q (proj_param q)
  // then something goes off the rails in inlining
  let result = (q.func q.param) in
  ()

val exampleFunc : t_Func U32.t
let exampleFunc e = ()

let main() : HST.St I32.t =
  let c = Closure_Cons exampleFunc 42ul in
  let res = invoke c in
  0l
