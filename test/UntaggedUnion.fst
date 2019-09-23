module UntaggedUnion

open LowStar.Union

/// An example
/// ==========

/// An example with a fictional type of messages, where some other information
/// in the context allows deducing the message and, hence, the particular case
/// of the union. Note that the invocation of ``union`` needs to be at the
/// top-level, and other occurrences of ``union`` are an extraction error.
type msg = | Msg1 | Msg2 | Msg3 | Msg4

/// The name (any_msg) and placement (right here) of the union typedef in C will
/// be determined via this top-level declaration.
let any_msg = union [
  Msg1, ("fst_msg", int);
  Msg2, ("snd_msg", int & int)
]

/// Convenient helpers 
inline_for_extraction noextract
let mk_ = mk any_msg

inline_for_extraction noextract
let proj_ = proj any_msg

/// The proof obligations here that Msg1 and Msg2 belong to msg_payload are
/// discharged by normalization.
let mk_msg (x: nat): any_msg (if x = 0 then Msg1 else Msg2) =
  if x = 0 then
    mk_ Msg1 (-1)
  else
    mk_ Msg2 (0, 0)

open FStar.Mul

let test (x: nat): int =
  let my_msg = mk_msg x in
  if x * x = 0 then
    proj_ Msg1 my_msg
  else
    fst (proj_ Msg2 my_msg)

// This one eschews nominal typing and will be flagged as an error by the
// tactic.
inline_for_extraction noextract
let mk_fail = mk (union [
  Msg1, ("fst_msg", int);
  Msg2, ("snd_msg", int & int)
])

[@ expect_failure ]
noextract
let bad =
  mk_fail Msg1 0
