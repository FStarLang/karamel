module TupleForwardDecl

// Test for a Karamel bug: when a parameterized struct has a pointer to a tuple
// type, Karamel fails to emit a forward declaration for the monomorphized tuple
// struct. This is because forward_kind in Monomorphization.ml returns None for
// tuple_lid (tuples are built-in and not in the type definition map), so
// insert_forward is a no-op. The resulting C code uses the tuple typedef before
// it is defined, causing a compilation error:
//   error: unknown type name 'K___...'
//
// This is the same bug triggered by Pulse.Lib.Slice.slice instantiated with
// a tuple type in the COSE/EverParse codebase.

open FStar.HyperStack.ST

module U32 = FStar.UInt32
module U64 = FStar.UInt64

#push-options "--__no_positivity"

// A parametric struct with a ref (pointer) to the type parameter,
// similar to Pulse.Lib.Slice.slice
noeq
type my_slice (a: Type0) : Type0 = {
  elt: ref a;
  len: U64.t;
}

// Using my_slice with a tuple parameter triggers the bug.
// Monomorphization visits my_slice<(U32.t & U64.t)>, encounters
// the ref (U32.t & U64.t) field, and tries to emit a forward
// declaration for the tuple. But forward_kind returns None for
// tuple_lid, so no forward declaration is emitted. The tuple's
// full definition may appear later or not at all.
noeq
type my_container = {
  data: my_slice (U32.t & U64.t);
  tag: U32.t;
}

#pop-options

let main () = 0l
