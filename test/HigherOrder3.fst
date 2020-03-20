module HigherOrder3

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module I32 = FStar.Int32

inline_for_extraction type t_Func (t_Param:Type) =
  r:HS.rid -> e:t_Param -> HST.St (unit)

noeq type t_Closure (t_Param:Type) =
  | Closure_Cons :
    func  : t_Func t_Param ->
    t_Closure t_Param

val createClosure (#t_Param:Type) (f:(t_Func t_Param)) : HST.St (t_Closure t_Param)
let createClosure #t_Param f = Closure_Cons f

val exampleFunc : t_Func I32.t
let exampleFunc r e = ()

let main() : HST.St I32.t =
  let p_q = createClosure exampleFunc in
  0l
