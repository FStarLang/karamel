module M

type t (i:bool) = { b:bool }

let f (x:t true) : bool = x.b
