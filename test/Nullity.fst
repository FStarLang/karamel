module Nullity

module B = FStar.Buffer
module HST = FStar.HyperStack.ST
open C.Nullity

let read (p: pointer UInt32.t): HST.Stack UInt32.t
  (fun h -> B.live h p) (fun _ _ _ -> True)
= !*p

let read_unit (p: pointer unit): HST.Stack unit
  (fun h -> B.live h p) (fun _ _ _ -> True)
= !*p

type pair = { first: UInt32.t; second: UInt32.t }

let read_field (p: pointer pair): HST.Stack UInt32.t
  (fun h -> B.live h p) (fun _ _ _ -> True)
= (!*p).first

let main () : Int32.t = 0l
