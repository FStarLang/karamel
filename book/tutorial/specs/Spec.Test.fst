module Spec.Test

/// It's really important to put spec tests in a separate module. Putting them
/// in ``Spec.Bignum`` would mean their encoding in the SMT solver would be fed
/// every time to Z3, polluting the context and slowing proofs down. Don't do that!

module S = FStar.Seq
#set-options "--lax"
module Spec = Spec.Bignum

let test (): bool =
  true
