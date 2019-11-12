module UntaggedUnion

open LowStar.Union

/// An example
/// ==========

/// An example with a fictional type of messages, where some other information
/// in the context allows deducing the message and, hence, the particular case
/// of the union. Note that the invocation of ``union`` needs to be at the
/// top-level, and other occurrences of ``union`` are an extraction error.
type msg = | Msg1 | Msg2 | Msg3 | Msg4

inline_for_extraction
let int32 = x:Int32.t { Int32.v x >= -1 /\ Int32.v x <= 1 }

/// The name (any_msg) and placement (right here) of the union typedef in C will
/// be determined via this top-level declaration.
let any_msg = union [
  Msg1, ("fst_msg", Int32.t);
  Msg2, ("snd_msg", Int32.t & Int32.t)
]

/// Convenient helpers
inline_for_extraction noextract
let cons_ = cons any_msg

inline_for_extraction noextract
let proj_ = proj any_msg

/// The proof obligations here that Msg1 and Msg2 belong to msg_payload are
/// discharged by normalization.
let cons_msg (x: Int32.t): any_msg (if x = 0l then Msg1 else Msg2) =
  if x = 0l then
    cons_ Msg1 1l
  else
    cons_ Msg2 (0l, 0l)

open FStar.Mul

let fst (x, y) = x

let test (x: int32): Int32.t =
  let my_msg = cons_msg x in
  if x `Int32.mul` x = 0l then
    proj_ Msg1 my_msg
  else
    fst (proj_ Msg2 my_msg)

// This one eschews nominal typing and will be flagged as an error by the
// tactic, but at use-site (see expect_failure below).
inline_for_extraction noextract
let cons_fail = cons (union [
  Msg1, ("fst_msg", Int32.t);
  Msg2, ("snd_msg", Int32.t & Int32.t)
])

[@ expect_failure ]
noextract
let bad =
  cons_fail Msg1 0l

let main () =
  test 1l
