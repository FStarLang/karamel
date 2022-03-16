module ExternErased

open FStar.Ghost

inline_for_extraction
let f_type = x:erased Int32.t -> Int32.t -> Int32.t
let f : f_type = fun _ b -> b

let g (f:f_type) = f (hide 0l) 1l
let test () = g f

[@@ CPrologue "int extern_test(int (*f)(int)) { return f(0); }"]
assume
val extern_test (f:f_type) : Int32.t

let main () = extern_test f
