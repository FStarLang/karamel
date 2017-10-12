module PConstant

module U32 = FStar.UInt32
open FStar.Char
open TestLib

let byte_thing c=
match c with
| 'a' -> 'b'
| _ -> c

