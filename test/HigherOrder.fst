module HigherOrder

open FStar.HyperStack
open FStar.HyperStack.ST

unfold
let bool_function = bool -> St bool

let const_f : bool_function = fun x -> x

let higher_id (f:bool_function) : bool_function = f

// this works, generating a call to [higher_id] and then a call to the x
// parameter due to [bool_function]
let still_const_f : bool_function =
  higher_id const_f

// on the other hand, after eta expansion KreMLin doesn't call higher_id correctly
let buggy_const_f (b:bool) =
  higher_id const_f b

// it turns out this function also extracts, and has an incorrect call already
inline_for_extraction [@"substitute"]
let inline_higher_id (f: bool_function) : bool_function =
  fun x -> higher_id f x

let still_buggy : bool_function =
  inline_higher_id const_f
