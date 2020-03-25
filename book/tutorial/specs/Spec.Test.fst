/// Specification test
/// ==================

module Spec.Test

/// It's really important to put spec tests in a separate module. Putting them
/// in ``Spec.Bignum`` would mean their encoding in the SMT solver would be fed
/// every time to Z3, polluting the context and slowing proofs down. Don't do that!

module S = FStar.Seq
module Spec = Spec.Bignum

open FStar.All

let test_v_vectors = [
  [ 4020757606ul; 24784186ul ], 106447272348738662;
  [ 1154478784ul; 20791736ul ], 89299827301544640
]

let test_v arg: ML _ =
  let s, v = arg in
  if Spec.v (S.seq_of_list s) <> v then
    failwith ("Spec.v is not equal to expected value " ^ string_of_int v)

let test (): ML _ =
  List.iter test_v test_v_vectors
