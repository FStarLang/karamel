module MacroAssumeVal

open FStar.Integers

(* A function-like macro with two arguments *)
[@ CMacro ]
assume val add_values: uint_32 -> uint_32 -> uint_32

(* A zero-argument constant-like macro *)
[@ CMacro ]
assume val magic_constant: uint_32

(* Use the function-like macro *)
let test_add (x y: uint_32) : uint_32 =
  add_values x y

(* Use the constant-like macro *)
let test_const () : uint_32 =
  magic_constant

(* Combine both *)
let main () : int_32 =
  let r = add_values (test_const ()) 1ul in
  if r = 0ul then 0l else 1l
