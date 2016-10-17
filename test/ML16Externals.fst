module ML16Externals

open FStar.ST
open FStar.Buffer

// This function will be implemented by us on the C side.
assume val print_int32: Int32.t -> Stack unit
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
