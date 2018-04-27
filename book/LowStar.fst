module LowStar

module B = FStar.Buffer

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
/// arithmetic within buffer bounds. In the formalization, structures are only
/// valid when allocated within a buffer.
///
/// This section describes Low* by example, showing valid and invalid
/// constructs, to give the reader a good grasp of what syntactic subset of the
/// F* language constitutes valid Low*.
///
/// **These snippets are all valid Low* constructs.**

// Supported: base types are machine integers, arithmetic is permitted
let square (x: UInt32.t): UInt32.t =
  let open FStar.UInt32 in
  x *%^ x

/// .. code:: c
///
///    uint32_t square(uint32_t x)
///    {
///      return x * x;
///    }
///
/// .. fst::

// Supported: classic control-flow
let abs (x: Int32.t): Pure Int32.t
  (requires Int32.v x <> Int.min_int 32)
  (ensures fun r -> Int32.v r >= 0)
=
  let open FStar.Int32 in
  if x >=^ 0l then
    x
  else
    0l -^ x

/// .. code:: c
///
///    int32_t abs(int32_t x)
///    {
///      if (x >= (int32_t)0)
///        return x;
///      else
///        return (int32_t)0 - x;
///    }
///
/// .. fst::

// Supported: stack allocation
let on_the_stack (): Stack UInt64.t (fun _ -> True) (fun _ _ _ -> True) =
  let open B in
  push_frame ();
  let b = B.create 0UL 64ul in
  b.(0ul) <- 32UL;
  let r = b.(0ul) in
  pop_frame ();
  r

/// .. code:: c
///
///    uint64_t on_the_stack()
///    {
///      uint64_t b[64U] = { 0U };
///      b[0U] = (uint64_t)32U;
///      uint64_t r = b[0U];
///      return r;
///    }
///
/// .. fst::

// Supported: heap allocation
let on_the_heap (): St UInt64.t =
  let open B in
  let b = B.rcreate_mm HyperStack.root 0UL 64ul in
  b.(0ul) <- 32UL;
  let r = b.(0ul) in
  B.rfree b;
  r

/// .. code:: c
///
///    uint64_t on_the_heap()
///    {
///      uint64_t *b = KRML_HOST_CALLOC((uint32_t)64U, sizeof (uint64_t));
///      b[0U] = (uint64_t)32U;
///      uint64_t r = b[0U];
///      KRML_HOST_FREE(b);
///      return r;
///    }
///
/// .. fst::

// Supported: defining a non-parameterized record made of Low* types
type uint128 = {
  low: UInt64.t;
  high: UInt64.t
}

/// .. code:: c
///
///    typedef struct uint128_s
///    {
///      uint64_t low;
///      uint64_t high;
///    }
///    uint128;
///
/// .. fst::

// Supported: records in buffers
let uint128_alloc (h l: UInt64.t): St (B.buffer uint128) =
  Buffer.rcreate_mm HyperStack.root ({ low = l; high = h }) 1ul

/// .. code:: c
///
///    uint128 *uint128_alloc(uint64_t h, uint64_t l)
///    {
///      KRML_CHECK_SIZE(sizeof (uint128), (uint32_t)1U);
///      uint128 *buf = KRML_HOST_MALLOC(sizeof (uint128));
///      buf[0U] = ((uint128){ .low = l, .high = h });
///      return buf;
///    }
///
/// .. fst::

// Supported: path access for records in buffers
let uint128_high (x: B.buffer uint128): Stack UInt64.t
  (requires fun h -> B.live h x /\ B.length x = 1)
  (ensures fun h0 _ h1 -> B.live h1 x)
=
  let open B in
  (x.(0ul)).high

/// .. code:: c
///
///    uint64_t uint128_high(uint128 *x)
///    {
///      return x->high;
///    }
///
/// .. fst::

// Supported: definition of global constants that evaluate to C constants, i.e.
// arithmetic over numerical constants, see the C11 standard for what exactly is
// allowed to be a constant.
let min_int32 = FStar.Int32.(0l -^ 0x7fffffffl -^ 1l)

/// .. code:: c
///
///    // Meta-evaluated by F*
///    int32_t min_int32 = (int32_t)-2147483648;
///
/// **These snippets are extensions to Low* (described in ??).**

// Extensions:
// - F*'s structural equality is compiled to a recursive C function
// - x and y are structures that are passed by value in C; this has performance
//   implications (see ??)
let uint128_equal (x y: uint128) =
  x = y

/// .. code:: c
///
///    static bool __eq__LowStar_uint128(uint128 y, uint128 x)
///    {
///      return true && x.low == y.low && x.high == y.high;
///    }
///
///    bool uint128_equal(uint128 x, uint128 y)
///    {
///      return __eq__LowStar_uint128(x, y);
///    }
///
/// .. fst::

// Extension: compiling F* inductives as tagged unions in C
noeq
type key =
  | Algorithm1: Buffer.buffer UInt32.t -> key
  | Algorithm2: Buffer.buffer UInt64.t -> key

/// .. code:: c
///
///    typedef enum { Algorithm1, Algorithm2 } key_tags;
///
///    typedef struct key_s
///    {
///      key_tags tag;
///      union {
///        uint32_t *case_Algorithm1;
///        uint64_t *case_Algorithm2;
///      }
///      ;
///    }
///    key;
///
/// .. fst::

// Extension: monomorphization of the option type
let abs2 (x: Int32.t): option Int32.t =
  let open FStar.Int32 in
  if x = min_int32 then
    None
  else if x >=^ 0l then
    Some x
  else
    Some (0l -^ x)

/// .. code:: c
///
///    typedef enum { FStar_Pervasives_Native_None, FStar_Pervasives_Native_Some }
///    FStar_Pervasives_Native_option__int32_t_tags;
///
///    typedef struct FStar_Pervasives_Native_option__int32_t_s
///    {
///      FStar_Pervasives_Native_option__int32_t_tags tag;
///      int32_t v;
///    }
///    FStar_Pervasives_Native_option__int32_t;
///
///    FStar_Pervasives_Native_option__int32_t abs2(int32_t x)
///    {
///      if (x == min_int32)
///        return ((FStar_Pervasives_Native_option__int32_t){ .tag = FStar_Pervasives_Native_None });
///      else if (x >= (int32_t)0)
///        return
///          ((FStar_Pervasives_Native_option__int32_t){ .tag = FStar_Pervasives_Native_Some, .v = x });
///      else
///        return
///          (
///            (FStar_Pervasives_Native_option__int32_t){
///              .tag = FStar_Pervasives_Native_Some,
///              .v = (int32_t)0 - x
///            }
///          );
///    }
///
/// .. fst::

// Extension: compilation of pattern matches
let fail_if #a #b (package: a * (a -> option b)): St b =
  let open C.Failure in
  let open C.String in
  let x, f = package in
  match f x with
  | None -> failwith !$"invalid argument: fail_if"
  | Some x -> x

/// .. code:: c
///
///    int32_t
///    fail_if__int32_t_int32_t(
///      K___int32_t_int32_t____FStar_Pervasives_Native_option__int32_t package
///    )
///    {
///      int32_t x = package.fst;
///      FStar_Pervasives_Native_option__int32_t (*f)(int32_t x0) = package.snd;
///      FStar_Pervasives_Native_option__int32_t scrut = f(x);
///      if (scrut.tag == FStar_Pervasives_Native_None)
///        return C_Failure_failwith__int32_t("invalid argument: fail_if");
///      else if (scrut.tag == FStar_Pervasives_Native_Some)
///      {
///        int32_t x1 = scrut.v;
///        return x1;
///      }
///      else
///      {
///        KRML_HOST_PRINTF("KreMLin abort at %s:%d\n%s\n",
///          __FILE__,
///          __LINE__,
///          "unreachable (pattern matches are exhaustive in F*)");
///        KRML_HOST_EXIT(255U);
///      }
///    }
///
/// .. fst::

// Extension: passing function pointers, monomorphization of tuple types as
// structs passed by value
let abs3 (x: Int32.t): St Int32.t =
  fail_if (x, abs2)

/// .. code:: c
///
///    int32_t abs3(int32_t x)
///    {
///      return
///        fail_if__int32_t_int32_t((
///            (K___int32_t_int32_t____FStar_Pervasives_Native_option__int32_t){ .fst = x, .snd = abs2 }
///          ));
///    }
///
/// .. fst::

// Extension: use meta-programming in F* to reduce local closures
let pow4 (x: UInt32.t): UInt32.t =
  let open FStar.UInt32 in
  [@ inline_let ]
  let pow2 (y: UInt32.t) = y *%^ y in
  pow2 (pow2 x)

/// .. code:: c
///
///    uint32_t pow4(uint32_t x)
///    {
///      uint32_t x0 = x * x;
///      return x0 * x0;
///    }
///
/// .. fst::

// Extension: definition of a global that does not compile to a C constant
let uint128_zero (): Tot uint128 =
  { high = 0UL; low = 0UL }

let zero = uint128_zero ()

/// .. code:: bash
///
///    $ krml -skip-linking -no-prefix LowStar LowStar.fst
///    (...)
///    Warning 9: : Some globals did not compile to C values and must be
///    initialized before starting main(). You did not provide a main function,
///    so users of your library MUST MAKE SURE they call kremlinit_globals();
///    (see kremlinit.c).
///
///    $ cat kremlinit.c
///    (...)
///    void kremlinit_globals()
///    {
///      zero = uint128_zero();
///    }
///
/// **These snippets are not Low*.**

// Cannot be compiled:
// - local recursive let-bindings are not Low*;
// - local closure captures variable in scope (KreMLin does not do closure conversion)
// - the list type is not Low*
let filter_map #a #b (f: a -> option b) (l: list a): list b =
  let rec aux (acc: list b) (l: list a): Tot (list b) (decreases l) =
    match l with
    | hd :: tl ->
        begin match f hd with
        | Some x -> aux (x :: acc) tl
        | None -> aux acc tl
        end
    | [] ->
        List.rev acc
  in
  aux [] l

/// Trying to compile the snippet above will generate a warning when calling F*
/// to generate a ``.krml`` file.
///
/// .. code:: bash
///
///    $ krml -skip-compilation -verbose LowStar.fst
///    ⚙ KreMLin auto-detecting tools.
///    (...)
///    ✔ [F*,extract]
///    <dummy>(0,0-0,0): (Warning 250) Error while extracting LowStar.filter_map
///    to KreMLin (Failure("Internal error: name not found aux\n"))
///
/// .. fst::

// Cannot be compiled: data types are compiled as flat structures in C, meaning
// that the list type would have infinite size in C. This is compiled by KreMLin
// but rejected by the C compiler. See ?? for an example of a linked list.
type list_int32 =
| Nil: list_int32
| Cons: hd:Int32.t -> tl:list_int32 -> list_int32

let mk_list (): St list_int32 =
  Cons 0l Nil

/// Trying to compile the snippet above will generate an error when calling the
/// C compiler to generate a ``.o`` file.
///
/// .. code:: bash
///
///    $ krml -skip-linking -verbose LowStar.fst
///    ⚙ KreMLin auto-detecting tools.
///    (...)
///    ✘ [CC,./LowStar.c]
///    In file included from ./LowStar.c:8:0:
///    ./LowStar.h:95:22: error: field ‘tl’ has incomplete type
///       LowStar_list_int32 tl;
///
/// .. fst::

// Cannot be compiled: polymorphic assume val; solution: make the function
// monomorphic, or provide a C macro
assume val pair_up: #a:Type -> #b:Type -> a -> b -> a * b

/// Trying to compile the snippet above will generate a warning when calling F*
/// to generate a ``.krml`` file.
///
/// .. code:: bash
///
///    $ krml -skip-compilation -verbose LowStar.fst
///    ⚙ KreMLin auto-detecting tools.
///    (...)
///    ✔ [F*,extract]
///    Not extracting LowStar.pair_up to KreMLin (polymorphic assumes are not supported)
///
/// .. fst::

// Cannot be compiled: indexed types. See section ?? for an unofficial KreMLin
// extension that works in some very narrow cases, or rewrite your code to make
// t an inductive. KreMLin currently does not have support for untagged unions,
// i.e. automatically making `t` a C union.
type alg = | Alg1 | Alg2
let t (a: alg) =
  match a with
  | Alg1 -> UInt32.t
  | Alg2 -> uint128

let default_t (a: alg): t a =
  match a with
  | Alg1 -> 0ul
  | Alg2 -> zero

/// Trying to compile the snippet above will generate invalid C code.
///
/// .. code:: c
///
///    void *default_t(alg a)
///    {
///      switch (a)
///      {
///        case Alg1:
///          {
///            return (void *)(uint32_t)0U;
///          }
///        case Alg2:
///          {
///            return (void *)zero
///          }
///        default:
///          {
///            KRML_HOST_PRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
///            KRML_HOST_EXIT(253U);
///          }
///      }
///    }
///
/// If you are lucky, the C compiler may generate an error:
///
/// .. code:: bash
///
///    $ krml -skip-linking LowStar.fst -add-include '"kremstr.h"' -no-prefix LowStar -warn-error +9
///
///    ✘ [CC,./LowStar.c]
///    ./LowStar.c: In function ‘default_t’:
///    ./LowStar.c:291:9: error: cannot convert to a pointer type
///             return (void *)zero;
///
/// .. _memory-model:
///
/// The memory model
/// ----------------
///
/// Beyond the language subset, one defining component of Low* is how it models
/// the C memory.
///
/// The F* HyperHeap model
/// ^^^^^^^^^^^^^^^^^^^^^^
///
/// F* is by default equipped with HyperHeap, a hierarchical memory model that
/// divides the heap into a tree of regions. This coarse-grained separation
/// allows the programmer to state modifies clauses at the level of regions, rather
/// than on individual references.
///
/// The HyperHeap memory model is described in the `2016 POPL paper
/// <https://www.fstar-lang.org/papers/mumon/>`_, as well as the `F* tutorial
/// <https://www.fstar-lang.org/tutorial>`_. We assume that the reader has a passing
/// degree of familiarity with HyperHeap.
///
/// The Low* HyperStack model
/// ^^^^^^^^^^^^^^^^^^^^^^^^^
///
/// Low* refines the HyperHeap memory model, adding a distinguished set of regions
/// that model the C call stack. Programs may use stack allocation, heap allocation
/// or both. The HyperStack memory model offers a set of effects that capture the
/// allocation behavior of functions.
///
/// The HyperStack memory model comprises the files
/// ``FStar.Monotonic.HyperStack.fst``, ``FStar.HyperStack.fst`` and
/// ``FStar.HyperStack.ST.fst`` in the ``ulib`` directory of F*.
///
/// .. note::
///
///    Many verification errors point to definitions in these three files. Being
///    familiar with these modules, their combinators and key concepts helps
///    understand why a given program fails to verify.

/// .. warning::
///
///    We recommend always defining the ``ST`` abbreviation at the beginning of
///    your module, in order to shadow the ``FStar.ST`` module, which is not
///    Low*.

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
///
/// The top-level region is the root, and is always a valid region. ``HS.rid``
/// is the type of regions.

let root: HS.rid = HS.root

/// Stack frames are modeled as distinguished regions that satisfy the
/// ``is_stack_region`` predicate. Allocating in a stack frame, unsurprisingly,
/// results in a stack-allocated variable or array in C. Stack frames may be
/// de-allocated as program execution progresses up the call stack, meaning that
/// the underlying HyperHeap region may disappear.
///
/// Regions that are not stack frames may *not* be de-allocated, and therefore
/// satisfy the ``is_eternal_region`` predicate. This includes the ``root``.
/// Allocating in one of these regions amounts to performing a heap allocation
/// in C.
///
/// Pushing a new stack frame amount to allocating a new stack region. In the
/// HyperHeap model, creating a new region requires a *parent*. Thus, when a
/// new stack frame is allocated, its parent is either the top-most stack frame,
/// or the ``root`` if no stack frame has been allocated so far.
///
/// .. warning ::
///
///     The ``root`` is not a stack region and does *not* satisfy ``is_stack_region``.
///
/// The most popular effect is the ``Stack`` effect, which takes:
///
/// - a precondition over the initial heap, of type ``HS.mem -> Type``, and a
/// - post-condition over the initial heap, the result, the final heap, of type
///   ``HS.mem -> a -> HS.mem -> Type``

effect Stack (a:Type) (pre: ST.st_pre) (post: (m0: HS.mem -> Tot (ST.st_post' a (pre m0)))) =
  STATE a
    (fun (p: ST.st_post a) (h: HS.mem) ->
      pre h /\ (forall a h1. (pre h /\ post h a h1 /\ ST.equal_domains h h1) ==> p a h1))

/// The relevant bit in this otherwise mundane definition is the
/// ``ST.equal_domains`` predicate.

let equal_domains (m0 m1: HS.mem) =
  m0.HS.tip == m1.HS.tip /\
  Set.equal (Map.domain m0.HS.h) (Map.domain m1.HS.h) /\
  ST.same_refs_in_all_regions m0 m1

/// The ``equal_domains`` predicate states that a function in the ``Stack`` effect:
///
/// - preserves the ``tip`` of the memory, i.e. calling this
///   function leaves the C call stack intact;
/// - does not allocate any new region on the heap, i.e. this is a
///   C function that does not heap-allocate;
/// - does not allocate in any existing region, i.e. this is a C
///   function that does not grow any existing stack frame on the call stack.
///
/// A function that satisfies these conditions is a function that can be safely
/// compiled as a C function. In other words, using the native C call stack as
/// an implementation of our model is correct.

let f (x: UInt32.t): Stack UInt32.t (fun _ -> True) (fun _ _ _ -> True) =
  FStar.UInt32.( x *%^ x )

/// Based on the knowledge above, consider the following failing function.
[@ fail ]
let g (): Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  let b = Buffer.create 0ul 8ul in
  ()

/// F* reports an assertion failure for the ``is_stack_region`` predicate.
/// Indeed, the ``create`` function requires that the ``tip`` be a valid stack
/// region, which is false when no stack frame has been pushed on the call stack.
///
/// One important insight at this stage is that F* does not "automatically"
/// enrich the verification context with the assumption that upon entering
/// ``g``, we have pushed a new stack frame. This would be the wrong thing to do
/// for a total function; furthermore, there is simply no such support in the language.
///
/// Rather, the user is expected to manually indicate which operations need to
/// conceptually happen in a new stack frame. The Low* memory model provides two
/// combinators for this purpose: ``push_frame`` and ``pop_frame``. The ``f``
/// function did not need them, because it performed no stateful operation.
///
/// .. note::
///
///    The following examples use the ``[@ fail ]`` F* attribute. Remember that
///    this tutorial is a valid F* file, which we put under continuous
///    integration and version control. This attribute merely indicates to F*
///    that the failure is intentional.
///
/// We can attempt to fix ``g`` by adding a call to ``push_frame``.
[@ fail ]
let g2 (): Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  push_frame ();
  let b = Buffer.create 0ul 8ul in
  ()

/// F* now reports an error for the ``equal_domains`` predicate above. Indeed,
/// the only way to leave the C call stack intact, and therefore satisfy the
/// requirements of the ``Stack`` effect, is to ensure we pop the stack
/// frame we just pushed.
let g3 (): Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  push_frame ();
  let b = Buffer.create 0ul 8ul in
  pop_frame ();
  ()

/// ``g3`` now successfully compiles to C:
///
/// .. code:: c
///
///    void g3()
///    {
///      uint32_t b[8U] = { 0U };
///    }

/// The ``Stack`` effect prevents heap allocation, hence ensuring that from the
/// caller's perspective, any heap ("eternal") regions remain unchanged.
///
/// For code that performs heap allocations, the libraries offer the ``ST``
/// effect. It is similar to the ``Stack`` effect, and takes the same form of
/// pre- and post-conditions, but allows heap allocation.

let g4 (): ST unit (fun _ -> True) (fun _ _ _ -> True) =
  push_frame ();
  let b = Buffer.rcreate_mm HS.root 0ul 8ul in
  pop_frame ();
  ()

/// The ``St`` effect might occasionally be convenient.

effect St (a:Type) = ST a (fun _ -> True) (fun _ _ _ -> True)

/// These are the basic building blocks of our memory model. Verifying on top of
/// this memory model involves reflecting the state of the memory at the proof
/// level, using the ``HS.mem`` type, and capturing the effect of allocations,
/// updates and de-allocations using suitable pre- and post-conditions. This can
/// be done using a combination of modifies clauses and libraries that reflect
/// low-level constructs, such as buffers and machine integers, at the proof
/// level. All of these are covered in the rest of this chapter.

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
