Low* language
=============

Low*, as formalized and presented in this `paper <https://arxiv.org/abs/1703.00053>`_,
is the first-order lambda calculus. Base types are booleans and
fixed-width integers. Low* has a primitive notion of *arrays* (also known as
buffers, although that terminology is being phased out) and pointer
arithmetic within buffer bounds. In the formalization, structures are only
valid when allocated within a buffer.

This section describes Low* by example, showing valid and invalid
constructs, to give the reader a good grasp of what syntactic subset of the
F* language constitutes valid Low*.

A crash course on Low*
----------------------

Base types
^^^^^^^^^^

This is only a brief introduction -- you should peruse existing bodies of code
(HACL*, EverCrypt, EverQuic) to get a good grasp of what is supported.

Low*'s base types are machine integers, booleans, units.

.. code:: fstar

  let square (x: UInt32.t): UInt32.t =
    let open FStar.UInt32 in
    x *%^ x

This, quite unexcitingly, compiles to the following C code:

.. code:: c

   uint32_t square(uint32_t x)
   {
     return x * x;
   }

Control-flow
^^^^^^^^^^^^

There are no restrictions on control-flow. Recursive functions are supported but
discouraged as you may be enjoying good performance only using a modern
compiler. (See further sections for loops.)

.. code:: fstar

  let abs (x: Int32.t): Pure Int32.t
    (requires Int32.v x <> Int.min_int 32)
    (ensures fun r -> Int32.v r >= 0)
  =
    let open FStar.Int32 in
    if x >=^ 0l then
      x
    else
      0l -^ x

.. code:: c

   int32_t abs(int32_t x)
   {
     if (x >= (int32_t)0)
       return x;
     else
       return (int32_t)0 - x;
   }

Allocations
^^^^^^^^^^^

Low* models stack allocation, which is covered in :ref:`buffer-library` below.
For now, you must use explicit push/pop combinators that model as the level of
the effect system the fact that a new stack frame exists and that all
allocations should be scoped to the lifetime of that stack frame. The ``Stack``
effect forces you to preserve the structure of the stack.

.. code:: fstar

    let on_the_stack (): Stack UInt64.t (fun _ -> True) (fun _ _ _ -> True) =
      push_frame ();
      let b = B.alloca 0UL 64ul in
      b.(0ul) <- 32UL;
      let r = b.(0ul) in
      pop_frame ();
      r

.. code:: c

   uint64_t on_the_stack()
   {
     uint64_t b[64U] = { 0U };
     b[0U] = (uint64_t)32U;
     uint64_t r = b[0U];
     return r;
   }

Low* supports heap allocation.

.. code:: fstar

    let on_the_heap (): St UInt64.t =
      let b = B.malloc HyperStack.root 0UL 64ul in
      b.(0ul) <- 32UL;
      let r = b.(0ul) in
      B.free b;
      r

.. code:: c

   uint64_t on_the_heap()
   {
     uint64_t *b = KRML_HOST_CALLOC((uint32_t)64U, sizeof (uint64_t));
     b[0U] = (uint64_t)32U;
     uint64_t r = b[0U];
     KRML_HOST_FREE(b);
     return r;
   }

Struct types
^^^^^^^^^^^^

Flat records are part of the original paper formalization, and are
translated as regular C ``struct``\ s.

.. code:: fstar

    type uint128 = {
      low: UInt64.t;
      high: UInt64.t
    }

.. code:: c

   typedef struct uint128_s
   {
     uint64_t low;
     uint64_t high;
   }
   uint128;

In the original paper, structs may be allocated within buffers.

.. code:: fstar

    let uint128_alloc (h l: UInt64.t): St (B.buffer uint128) =
      B.malloc HyperStack.root ({ low = l; high = h }) 1ul

.. code:: c

   uint128 *uint128_alloc(uint64_t h, uint64_t l)
   {
     KRML_CHECK_SIZE(sizeof (uint128), (uint32_t)1U);
     uint128 *buf = KRML_HOST_MALLOC(sizeof (uint128));
     buf[0U] = ((uint128){ .low = l, .high = h });
     return buf;
   }

Still in the original paper, one may access a buffer index, then select a
number of fields.

.. code:: fstar

    let uint128_high (x: B.buffer uint128): Stack UInt64.t
      (requires fun h -> B.live h x /\ B.length x = 1)
      (ensures fun h0 _ h1 -> B.live h1 x)
    =
      (x.(0ul)).high

.. code:: c

   uint64_t uint128_high(uint128 *x)
   {
     return x->high;
   }

Constants
^^^^^^^^^

One may define global constants too, as long as they evaluate to C
constants. As a rough approximation, arithmetic expressions and addresses of
other globals are C constants, but as always, the `C11 standard
<http://open-std.org/jtc1/SC22/wg14/www/docs/n1548.pdf>`_ is the ultimate
source of truth.

.. code:: fstar

    let min_int32 = FStar.Int32.(0l -^ 0x7fffffffl -^ 1l)

.. code:: c

   // Meta-evaluated by F*
   int32_t min_int32 = (int32_t)-2147483648;

Extensions to Low*
------------------

KreMLin supports a number of programming patterns beyond the original paper
formalization, which aim to maximize programmer productivity. We now review
the main ones.

Equalities monomorphization
^^^^^^^^^^^^^^^^^^^^^^^^^^^

One can rely on KreMLin to compile F*'s structural equality (the ``(=)``
operator) to C functions specialized to each type. Furthermore, the function
below demonstrates the use of a struct type as a value, which is
straightforwardly compiled to a C structure passed by value. Be aware that doing
so has performance implications (see ??).

.. code:: fstar

    let uint128_equal (x y: uint128) =
      x = y

.. code:: c

   static bool __eq__LowStar_uint128(uint128 y, uint128 x)
   {
     return true && x.low == y.low && x.high == y.high;
   }

   bool uint128_equal(uint128 x, uint128 y)
   {
     return __eq__LowStar_uint128(x, y);
   }

Inductives as tagged unions; pattern-matching compilation
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

One may also use F* inductives, knowing that KreMLin will compile them as
tagged unions. There are currently five different compilation schemes for data
types that all aim to generate C code that is "as natural" as possible:

- inductives with a single branch with a single argument are completely
  eliminated (e.g. ``type t = | Foo: x:UInt32.t -> t`` compiles to ``uint32_t``)
- inductives with only constant constructors compile to ``uint8`` (or a C11 enum
  if ``-fnoshort-enums``  is used (e.g. ``type t = | A | B`` compiles to
  ``uint8``)
- inductives with a single constructor compile to a C struct without a tag (e.g.
  ``type t = | Foo: x:UInt32.t -> y:UInt32.t -> t`` compiles to ``typedef struct
  { uint32_t x; uint32_t y } t``)
- inductives with a single non-constant constructor compile to a tagged C struct
  without a union (e.g. ``type option_int = | None' | Some' of UInt32.t``
  compiles to ``typedef struct { uint8_t option_int_tag; uint32_t x }
  option_int``)
- all other inductives are compiled as tagged unions.

For instance, the data type below does not enjoy any optimized compilation
scheme and generates a complete tagged union.

.. code:: fstar

    noeq
    type key =
      | Algorithm1: B.buffer UInt32.t -> key
      | Algorithm2: B.buffer UInt64.t -> key

.. code:: c

   typedef enum { Algorithm1, Algorithm2 } key_tags;

   typedef struct key_s
   {
     key_tags tag;
     union {
       uint32_t *case_Algorithm1;
       uint64_t *case_Algorithm2;
     }
     ;
   }
   key;

Data type monomorphization
^^^^^^^^^^^^^^^^^^^^^^^^^^

Generally, KreMLin performs a whole-program monomorphization of
parameterized data types. The example below demonstrates this, along with a
"pretty" compilation scheme for the option type that does not involves an
anonymous union.

.. code:: fstar

    let abs2 (x: Int32.t): option Int32.t =
      let open FStar.Int32 in
      if x = min_int32 then
        None
      else if x >=^ 0l then
        Some x
      else
        Some (0l -^ x)

.. code:: c

   typedef enum { FStar_Pervasives_Native_None, FStar_Pervasives_Native_Some }
   FStar_Pervasives_Native_option__int32_t_tags;

   typedef struct FStar_Pervasives_Native_option__int32_t_s
   {
     FStar_Pervasives_Native_option__int32_t_tags tag;
     int32_t v;
   }
   FStar_Pervasives_Native_option__int32_t;

   FStar_Pervasives_Native_option__int32_t abs2(int32_t x)
   {
     if (x == min_int32)
       return ((FStar_Pervasives_Native_option__int32_t){ .tag = FStar_Pervasives_Native_None });
     else if (x >= (int32_t)0)
       return
         ((FStar_Pervasives_Native_option__int32_t){ .tag = FStar_Pervasives_Native_Some, .v = x });
     else
       return
         (
           (FStar_Pervasives_Native_option__int32_t){
             .tag = FStar_Pervasives_Native_Some,
             .v = (int32_t)0 - x
           }
         );
   }

Pattern matches compilation
^^^^^^^^^^^^^^^^^^^^^^^^^^^

Inductives are compiled by KreMLin, and so are pattern matches. Note that
for a series of cascading if-then-elses, KreMLin has to insert a fallback
else statement, both because the original F* code may be unverified and the
pattern-matching may be incomplete, but also because the C compiler may
trigger an error.

.. code:: fstar

    let fail_if #a #b (package: a * (a -> option b)): St b =
      let open C.Failure in
      let open C.String in
      let x, f = package in
      match f x with
      | None -> failwith !$"invalid argument: fail_if"
      | Some x -> x

.. code:: c

   int32_t
   fail_if__int32_t_int32_t(
     K___int32_t_int32_t____FStar_Pervasives_Native_option__int32_t package
   )
   {
     int32_t x = package.fst;
     FStar_Pervasives_Native_option__int32_t (*f)(int32_t x0) = package.snd;
     FStar_Pervasives_Native_option__int32_t scrut = f(x);
     if (scrut.tag == FStar_Pervasives_Native_None)
       return C_Failure_failwith__int32_t("invalid argument: fail_if");
     else if (scrut.tag == FStar_Pervasives_Native_Some)
     {
       int32_t x1 = scrut.v;
       return x1;
     }
     else
     {
       KRML_HOST_PRINTF("KreMLin abort at %s:%d\n%s\n",
         __FILE__,
         __LINE__,
         "unreachable (pattern matches are exhaustive in F*)");
       KRML_HOST_EXIT(255U);
     }
   }

Function monomorphization
^^^^^^^^^^^^^^^^^^^^^^^^^

As demonstrated above, functions also get monomorphized based on their
instances. Note that using a polymorphic type in an ``assume val`` is not
supported.


Higher order with functions pointers
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Higher order is, to a certain extent, possible (i.e. as long as you don't use
closures). The sample above
demonstrates a block-scope function pointer. The ``fail_if`` function has
been specialized on ``K__int32_t_int32_t``, which is itself a specialization
of the polymorphic pair type of F*. Below is a sample caller of
``fail_if__int32_t_int32_t``, which relies on passing a pair of a function
pointer and its argument.

.. code:: fstar

    let abs3 (x: Int32.t): St Int32.t =
      fail_if (x, abs2)

.. code:: c

   int32_t abs3(int32_t x)
   {
     return
       fail_if__int32_t_int32_t((
           (K___int32_t_int32_t____FStar_Pervasives_Native_option__int32_t){ .fst = x, .snd = abs2 }
         ));
   }

Local closures are not supported, as they do not have a natural compilation
scheme to C. You can, however, rely on ``[@inline_let]`` to define local
helpers.

.. code:: fstar

    let pow4 (x: UInt32.t): UInt32.t =
      let open FStar.UInt32 in
      [@ inline_let ]
      let pow2 (y: UInt32.t) = y *%^ y in
      pow2 (pow2 x)

.. code:: c

   uint32_t pow4(uint32_t x)
   {
     uint32_t x0 = x * x;
     return x0 * x0;
   }

If this is not workable, you will have to define the closure state
yourself, carry it around, and apply the closure to its environment manually.

Non-constant globals
^^^^^^^^^^^^^^^^^^^^

In the case that the user defines a global variable that does not compile to
a C11 constant, KreMLin generates a "static initializer" in the special
``kremlinit_globals`` function. If the program has a ``main``, KreMLin
automatically prepends a call to ``kremlinit_globals`` in the ``main``. If
the program does not have a ``main`` and is intended to be used as a
library, KreMLin emits a warning, which is fatal by default.

.. code:: fstar

    let uint128_zero (): Tot uint128 =
      { high = 0UL; low = 0UL }

    let zero = uint128_zero ()

.. code:: bash

   $ krml -skip-linking -no-prefix LowStar LowStar.fst
   (...)
   Warning 9: : Some globals did not compile to C values and must be
   initialized before starting main(). You did not provide a main function,
   so users of your library MUST MAKE SURE they call kremlinit_globals();
   (see kremlinit.c).

   $ cat kremlinit.c
   (...)
   void kremlinit_globals()
   {
     zero = uint128_zero();
   }

Code quality improvements
-------------------------

In addition to all the features describe above, KreMLin will go great lengths to
generate readable code. Here are some of the optimization passes performed.

Unused argument elimination
^^^^^^^^^^^^^^^^^^^^^^^^^^^

There are three unused argument elimination passes.

*Type-based* argument elimination removes all unit arguments to functions,
everywhere, always. (This is particularly useful if your functions take
``Ghost.erased`` arguments.)

*Usage-based* argument elimination removes unused arguments to functions *only*
if they are private to the current module and do not appear in the header *and*
if they are only used in a first-order setting, i.e. always used as the head of
a fully applied function call.

*Data type* argument elimination removes type parameters from types that don't
use them; it also removes unit arguments to constructors, i.e. your C type
declarations should never have a unit field.

Temporary variable elimination
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

F* introduces a significant amount of temporary variables called ``uu___``,
owing to its monadic let semantics. (You can see these variables looking at the
generated OCaml code.) KreMLin uses two different syntactic criteria to get rid
of those.

Tuple elimination
^^^^^^^^^^^^^^^^^

To avoid allocating too many intermediary values of monomorphized tuple types,
KreMLin applies the following two rules before data type compilation &
monomorphization:

.. code::

  (i)   match (e1, e2) with (x, y) -> e  ~~~>
        let x = e1 in let y = e2 in e
  (ii)  match let x = e0 in (e1, e2) with (x, y) -> e  ~~~>
        let x = e0 in match (e1, e2) with (x, y) -> e

This is absolutely crucial to share code between specs and implementations. See
the toy project for an example in action.

Dead code elimination
^^^^^^^^^^^^^^^^^^^^^

Any code that becomes unreachable after bundling (see advanced topics) is
automatically removed.

Unused local variable elimination
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Using a syntactic criterion, local variables that have no observable
side-effects are eliminated.

Functional update optimization
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Code that mutakes a single field of a struct in place compiles to a C mutation.

.. code:: fstar

  b.(0) <- { b.(0) with f = e }

gives:

.. code:: c

  b->f = e;


Some non-Low* code
------------------

We now review some classic programming patterns that are not supported in
Low*.

The example below cannot be compiled for the following reasons:

- local recursive let-bindings are not Low*;
- local closure captures variable in scope (KreMLin does not do closure conversion)
- the list type is not Low*.

.. code:: fstar

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

Trying to compile the snippet above will generate a warning when calling F*
to generate a ``.krml`` file.

.. code:: bash

   $ krml -skip-compilation -verbose LowStar.fst
   ⚙ KreMLin auto-detecting tools.
   (...)
   ✔ [F*,extract]
   <dummy>(0,0-0,0): (Warning 250) Error while extracting LowStar.filter_map
   to KreMLin (Failure("Internal error: name not found aux\n"))

To explain why the list type cannot be compiled to C, consider the snippet
below. Data types are compiled as flat structures in C, meaning that the
list type would have infinite size in C. This is compiled by KreMLin but
rejected by the C compiler. See ?? for an example of a linked list.

.. code:: fstar

  type list_int32 =
  | Nil: list_int32
  | Cons: hd:Int32.t -> tl:list_int32 -> list_int32

  let mk_list (): St list_int32 =
    Cons 0l Nil

Trying to compile the snippet above will generate an error when calling the
C compiler to generate a ``.o`` file.

.. code:: bash

   $ krml -skip-linking -verbose LowStar.fst
   ⚙ KreMLin auto-detecting tools.
   (...)
   ✘ [CC,./LowStar.c]
   In file included from ./LowStar.c:8:0:
   ./LowStar.h:95:22: error: field ‘tl’ has incomplete type
      LowStar_list_int32 tl;

Polymorphic assumes are also not compiled. KreMLin could generate one C
``extern`` declaration per monomorphic use, but this would require the user
to provide a substantial amount of manually-written code, so instead we
refuse to compile the definition below.

.. code:: fstar

    // Cannot be compiled: polymorphic assume val; solution: make the function
    // monomorphic, or provide a C macro
    assume val pair_up: #a:Type -> #b:Type -> a -> b -> a * b

Trying to compile the snippet above will generate a warning when calling F*
to generate a ``.krml`` file.

.. code:: bash

   $ krml -skip-compilation -verbose LowStar.fst
   ⚙ KreMLin auto-detecting tools.
   (...)
   ✔ [F*,extract]
   Not extracting LowStar.pair_up to KreMLin (polymorphic assumes are not supported)

One point worth mentioning is that indexed types are by default not
supported. See section ?? for an unofficial KreMLin extension that works in
some very narrow cases, or rewrite your code to make ``t`` an inductive. KreMLin
currently does not have support for untagged unions, i.e. automatically
making ``t`` a C union.

.. code:: fstar

    type alg = | Alg1 | Alg2
    let t (a: alg) =
      match a with
      | Alg1 -> UInt32.t
      | Alg2 -> uint128

    let default_t (a: alg): t a =
      match a with
      | Alg1 -> 0ul
      | Alg2 -> zero

Trying to compile the snippet above will generate invalid C code.

.. code:: c

   // The void* is the sign that something was not type-able in Low* and was
   // sent to the Top type.
   void *default_t(alg a)
   {
     switch (a)
     {
       case Alg1:
         {
           return (void *)(uint32_t)0U;
         }
       case Alg2:
         {
           return (void *)zero
         }
       default:
         {
           KRML_HOST_PRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
           KRML_HOST_EXIT(253U);
         }
     }
   }

If you are lucky, the C compiler may generate an error:

.. code:: bash

   $ krml -skip-linking LowStar.fst -add-include '"kremstr.h"' -no-prefix LowStar -warn-error +9

   ✘ [CC,./LowStar.c]
   ./LowStar.c: In function ‘default_t’:
   ./LowStar.c:291:9: error: cannot convert to a pointer type
            return (void *)zero;
