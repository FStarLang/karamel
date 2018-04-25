module LowStar

open FStar.HyperStack.ST

/// The Low* subset of F*
/// =====================
///
/// The language subset
/// -------------------
///
/// Low*, as formalized and presented on `paper <https://arxiv.org/abs/1703.00053>`_,
/// is the first-order lambda calculus. Base types are booleans and
/// fixed-width integers. Low* has a primitive notion of *buffers* and pointer
/// arithmetic within buffer bounds.
///
/// These snippets are all valid Low* constructs.

let square (x: UInt32.t): UInt32.t =
  let open FStar.UInt32 in
  x *%^ x

let abs (x: Int32.t): Pure Int32.t
  (requires Int32.v x <> Int.min_int 32)
  (ensures fun r -> Int32.v r >= 0)
=
  let open FStar.Int32 in
  if x >=^ 0l then
    x
  else
    0l -^ x

/// These snippets are extensions to Low* (described in ??).

let min_int32 = FStar.Int32.(0l -^ 0x7fffffffl -^ 1l)


// Extension: compiling F* inductives as structures passed by value in C
type uint128 = {
  low: UInt64.t;
  high: UInt64.t
}

// Extension: F*'s structural equality is compiled to a C function
let uint128_equal (x y: uint128) =
  x = y

// Extension: compiling F* inductives as tagged unions in C
noeq
type key =
  | Algorithm1: Buffer.buffer UInt32.t -> key
  | Algorithm2: Buffer.buffer UInt64.t -> key

// Extension: monomorphization of the option type
let abs2 (x: Int32.t): option Int32.t =
  let open FStar.Int32 in
  if x = min_int32 then
    None
  else if x >=^ 0l then
    Some x
  else
    Some (0l -^ x)

// Extension: compilation of pattern matches
let fail_if #a #b (package: a * (a -> option b)): St b =
  let open C.Failure in
  let open C.String in
  let x, f = package in
  match f x with
  | None -> failwith !$"invalid argument: fail_if"
  | Some x -> x

// Extension: passing function pointers, monomorphization of tuple types as structs passed by value
let abs3 (x: Int32.t): St Int32.t =
  fail_if (x, abs2)

/// These snippets are not Low*.

// Cannot be compiled: closure; solution: hoist the closure to a top-level function
let pow4 (x: UInt32.t): UInt32.t =
  let open FStar.UInt32 in
  let pow2 (y: UInt32.t) = y *%^ y in
  pow2 (pow2 x)

// Cannot be compiled: polymorphic assume val; solution: make the function monomorphic, or provide a C macro
assume val pair_up: #a:Type -> #b:Type -> a -> b -> a * b

// Cannot be compiled: an untagged union over types that are non-pointers; see section ?? for an unofficial KreMLin extension, or rewrite your code to use a data type
type alg = | Alg1 | Alg2
let key' (a: alg) =
  match a with
  | Alg1 -> Buffer.buffer UInt32.t
  | Alg2 -> Buffer.buffer UInt64.t
  
///
/// .. _memory-model:
///
/// The memory model
/// ----------------
///
/// The C memory is traditionally presented as a combination of a *stack* and a
/// *heap*. Each function call
///
/// The core libraries
/// ------------------
///
/// Low* is made up of a few primitive libraries that enjoy first-class support in
/// KreMLin. These core libraries are typically made up of a model (an ``.fst``
/// file) and an interface (an ``.fsti`` file). Verification is performed against
/// the model, but at extraction-time, the model is replaced with primitive C
/// constructs.
///
/// .. _machine-integers:
///
/// The machine integer libraries
/// ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
///
/// Machine integers are modeled as natural numbers that fit within a certain number
/// of bits. This model is dropped by KreMLin, in favor of C's fixed-width types.
///
/// .. _buffer-library:
///
/// The buffer library
/// ^^^^^^^^^^^^^^^^^^
///
/// The workhouse of Low*, the buffer library is modeled as a reference to a
/// sequence. Sequences are not meant to be extracted to C: KreMLin drops this
/// sequence-based model, in favor of C's stack- or heap-allocated arrays.
///
/// .. _modifies-library:
///
/// The modifies clauses library
/// ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
///
/// .. _c-library:
///
/// Loops and other C concepts
/// ^^^^^^^^^^^^^^^^^^^^^^^^^^
