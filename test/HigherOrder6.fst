module HigherOrder6

module I32 = FStar.Int32
module B = LowStar.Buffer
module HST = FStar.HyperStack.ST
module HS = FStar.HyperStack

type t_F (a:Type) = B.pointer a -> HST.St (unit)

let bar (#a:Type) (p:t_F a) : HST.St (unit) = ()

type t_D (r:HS.rid) = 
| D_Cons :
    rCopy : (v:HS.rid{ v = r}) ->
    len : (I32.t) ->
    t_D r

val foo (a:Type) : t_F (a)
let foo a p = ()

let main() : HST.St I32.t 
=
let r = HST.new_region HS.root in
let f = foo (t_D r) in
let x = bar f in
0l
