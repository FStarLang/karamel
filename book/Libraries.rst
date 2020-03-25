Low* core libraries
===================

Low* is made up of a few primitive libraries that enjoy first-class support in
KreMLin. These core libraries are typically made up of a model (an ``.fst``
file) and an interface (an ``.fsti`` file). Verification is performed against
the model, but at extraction-time, the model is replaced with primitive C
constructs.

.. _memory-model:

The memory model
----------------

Beyond the language subset, one defining component of Low* is how it models
the C memory.

The F* HyperHeap model
^^^^^^^^^^^^^^^^^^^^^^

F* is by default equipped with HyperHeap, a hierarchical memory model that
divides the heap into a tree of regions. This coarse-grained separation
allows the programmer to state modifies clauses at the level of regions, rather
than on individual references.

The HyperHeap memory model is described in the `2016 POPL paper
<https://www.fstar-lang.org/papers/mumon/>`_, as well as the `F* tutorial
<https://www.fstar-lang.org/tutorial>`_. We assume that the reader has a passing
degree of familiarity with HyperHeap.

The HyperStack model
^^^^^^^^^^^^^^^^^^^^

Low* refines the HyperHeap memory model, adding a distinguished set of regions
that model the C call stack. Programs may use stack allocation, heap allocation
or both. The HyperStack memory model offers a set of effects that capture the
allocation behavior of functions.

The HyperStack memory model comprises the files
``FStar.Monotonic.HyperStack.fst``, ``FStar.HyperStack.fst`` and
``FStar.HyperStack.ST.fst`` in the ``ulib`` directory of F*.

.. note::

   Many verification errors point to definitions in these three files. Being
   familiar with these modules, their combinators and key concepts helps
   understand why a given program fails to verify.

.. warning::

   We recommend always defining the ``ST`` abbreviation at the beginning of
   your module, in order to shadow the ``FStar.ST`` module, which is not
   Low*.

.. code:: fstar

  module ST = FStar.HyperStack.ST
  module HS = FStar.HyperStack


The top-level region is the root, and is always a valid region. ``HS.rid``
is the type of regions.

.. code:: fstar

  let root: HS.rid = HS.roo

Stack frames are modeled as distinguished regions that satisfy the
``is_stack_region`` predicate. Allocating in a stack frame, unsurprisingly,
results in a stack-allocated variable or array in C. Stack frames may be
de-allocated as program execution progresses up the call stack, meaning that
the underlying HyperHeap region may disappear.

Regions that are not stack frames may *not* be de-allocated, and therefore
satisfy the ``is_eternal_region`` predicate. This includes the ``root``.
Allocating in one of these regions amounts to performing a heap allocation
in C.

Pushing a new stack frame amount to allocating a new stack region. In the
HyperHeap model, creating a new region requires a *parent*. Thus, when a
new stack frame is allocated, its parent is either the top-most stack frame,
or the ``root`` if no stack frame has been allocated so far.

.. warning::

    The ``root`` is not a stack region and does *not* satisfy ``is_stack_region``.

.. code:: fstar

  let _ =
    HS.root_is_not_freeable ();
    assert (ST.is_eternal_region root /\ ~ (Monotonic.HyperStack.is_stack_region root))


The most popular effect is the ``Stack`` effect, which takes:

- a precondition over the initial heap, of type ``HS.mem -> Type``, and a
- post-condition over the initial heap, the result, the final heap, of type
  ``HS.mem -> a -> HS.mem -> Type``

.. code:: fstar

    effect Stack (a:Type) (pre: ST.st_pre) (post: (m0: HS.mem -> Tot (ST.st_post' a (pre m0)))) =
      STATE a
        (fun (p: ST.st_post a) (h: HS.mem) ->
          pre h /\ (forall a h1. (pre h /\ post h a h1 /\ ST.equal_domains h h1) ==> p a h1))

The relevant bit in this otherwise mundane definition is the
``ST.equal_domains`` predicate.

.. code:: fstar

    let equal_domains (m0 m1: HS.mem) =
      (HS.get_tip m0) == (HS.get_tip m1) /\
      Set.equal (Map.domain (HS.get_hmap m0)) (Map.domain (HS.get_hmap m1)) /\
      ST.same_refs_in_all_regions m0 m1

The ``equal_domains`` predicate states that a function in the ``Stack`` effect:

- preserves the ``tip`` of the memory, i.e. calling this
  function leaves the C call stack intact;
- does not allocate any new region on the heap, i.e. this is a
  C function that does not heap-allocate;
- does not allocate in any existing region, i.e. this is a C
  function that does not grow any existing stack frame on the call stack.

A function that satisfies these conditions is a function that can be safely
compiled as a C function. In other words, using the native C call stack is a
valid implementation of our model.

.. code:: fstar

    let f (x: UInt32.t): Stack UInt32.t (fun _ -> True) (fun _ _ _ -> True) =
      FStar.UInt32.( x *%^ x )


Based on the knowledge above, consider the following failing function.

.. code:: fstar

    [@ expect_failure ]
    let g (): Stack unit (fun _ -> True) (fun _ _ _ -> True) =
      let b = B.alloca 0ul 8ul in
      ()

F* reports an assertion failure for the ``is_stack_region`` predicate.
Indeed, the ``alloca`` function requires that the ``tip`` be a valid stack
region, which is false when no stack frame has been pushed on the call stack.

One important insight at this stage is that F* does not "automatically"
enrich the verification context with the assumption that upon entering
``g``, we have pushed a new stack frame. This would be the wrong thing to do
for a total function; furthermore, there is simply no such support in the language.

Rather, the user is expected to manually indicate which operations need to
conceptually happen in a new stack frame. The Low* memory model provides two
combinators for this purpose: ``push_frame`` and ``pop_frame``. The ``f``
function did not need them, because it performed no stateful operation.

We can attempt to fix ``g`` by adding a call to ``push_frame``.

.. code:: fstar

    [@ expect_failure ]
    let g2 (): Stack unit (fun _ -> True) (fun _ _ _ -> True) =
      push_frame ();
      let b = B.alloca 0ul 8ul in
      ()

F* now reports an error for the ``equal_domains`` predicate above. Indeed,
the only way to leave the C call stack intact, and therefore satisfy the
requirements of the ``Stack`` effect, is to ensure we pop the stack
frame we just pushed.

.. code:: fstar

    let g3 (): Stack unit (fun _ -> True) (fun _ _ _ -> True) =
      push_frame ();
      let b = B.alloca 0ul 8ul in
      pop_frame ();
      ()

``g3`` now successfully compiles to C:

.. code:: c

   void g3()
   {
     uint32_t b[8U] = { 0U };
   }

The ``Stack`` effect prevents heap allocation, hence ensuring that from the
caller's perspective, any heap ("eternal") regions remain unchanged.

For code that performs heap allocations, the libraries offer the ``ST``
effect. It is similar to the ``Stack`` effect, and takes the same form of
pre- and post-conditions, but allows heap allocation.

.. code:: fstar

    let g4 (): ST unit (fun _ -> True) (fun _ _ _ -> True) =
      push_frame ();
      let b = B.malloc HS.root 0ul 8ul in
      pop_frame ();
      ()

The ``St`` effect might occasionally be convenient.

.. code:: fstar

    effect St (a:Type) = ST a (fun _ -> True) (fun _ _ _ -> True)

One can reflect the memory as an ``HS.mem`` at any program point, by using
``ST.get ()``.

.. code:: fstar

    let test_st_get (): St unit =
      push_frame ();
      let m = ST.get () in
      assert (Monotonic.HyperStack.is_stack_region (HS.get_tip m));
      pop_frame ()

These are the basic building blocks of our memory model. Verifying on top of
this memory model involves reflecting the state of the memory at the proof
level, using the ``HS.mem`` type, and capturing the effect of allocations,
updates and de-allocations using suitable pre- and post-conditions. This can
be done using a combination of modifies clauses and libraries that reflect
low-level constructs, such as buffers and machine integers, at the proof
level. All of these are covered in the rest of this chapter.

Advanced: the ``StackInline`` effect
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

TODO

.. _machine-integers:

Machine integers
----------------

Machine integers are modeled as natural numbers that fit within a certain number
of bits. This model is dropped by KreMLin, in favor of C's fixed-width types.

Fixed-width integers are found in ``FStar.UInt{16,32,64,128}.fst`` and
``FStar.Int{16,32,64,128}``. The ``FStar.Int.Cast.Full.fst`` module offers
conversion functions between these integer types.

.. warning ::

   By default, KreMLin relies on the non-standard ``unsigned __int128`` C
   type to implement ``FStar.UInt128.t``. This type is widely supported
   across GCC and Clang versions, but not by the Microsoft compilers. If you
   need 128-bit unsigned integers, consider reading
   ``kremlib/README.md``, which offers both an MSVC-specific alternative,
   and a portable, albeit slower, implementation.

Machine integers offer the classic set of arithmetic operations. Like in C,
unsigned integers have wraparound overflow semantics, exposed via the
``add_mod`` function. Signed integers offer no such function. Other
undefined behaviors of C are ruled out at the F* level, such as shifting an
integer by the bit width.

.. note ::

   In addition to classic arithmetic operations, some modules offer
   constant-time operations such as ``eq_mask`` and ``gte_mask``, which
   allow defining a "secret integer" module on top of these integers, that
   offers no comparison operator returning a boolean, to avoid timing leaks. See
   the HACL* libraries for secret integers.

Machine integers modules also define operators, suffixed with ``^``. For
instance, the ``+`` operation for ``UInt32`` is ``+^``. Wraparound variants
have an extra ``%`` character, such as ``+%^``, when available.

.. note ::

   The unary minus is broken for machine integers.
   This does not parse: ``let x = UInt32.(-^ 0ul)``

Operators follow the standard precedence rules of F*, which are outlined on
its `wiki
<https://github.com/FStarLang/FStar/wiki/Parsing-and-operator-precedence>`_.
Operators are resolved in the current scope; we recommend the use of module
abbreviations and the let-open notation ``M.( ... )``.

.. code:: fstar

    module U32 = FStar.UInt32

    let z = U32.(16ul -^ 8ul )

.. note ::

    By default, operations require that the caller prove that the result fits in
    the given integer width. For instance, ``U32.add`` has ``(requires (size (v
    a + v b) n))`` as a precondition. Look at ``U32.add_modulo`` for no
    precondition.

Machine integers can be reflected as natural numbers of type ``nat`` using
the ``v`` function. It is generally more convenient to perform proofs on
natural numbers.

.. code:: fstar

    let test_v (): unit =
      let x = 0ul in
      assert (U32.v x = 0)

.. _buffer-library:

The buffer library
------------------

``LowStar.Buffer`` is the workhorse of Low*, and allows modeling C arrays on
the stack and in the heap. ``LowStar.Buffer`` models C arrays as follows:

.. code:: fstar

    let lseq (a: Type) (l: nat) : Type =
      (s: Seq.seq a { Seq.length s == l } )

    noeq
    type buffer (a:Type) =
      | MkBuffer: max_length:UInt32.t
        -> content:reference (lseq a (U32.v max_length))
        -> idx:UInt32.t
        -> length:UInt32.t{U32.(v idx + v length <= v max_length)}
        -> buffer a

In other words, buffers are modeled as a reference to a sequence, along with
a starting index ``idx``, and a ``length``, which captures how much of an
allocation slice one is currently pointing to.

This is a model: at compilation-time, KreMLin implements buffers using C arrays.

**The length** is available in ghost (proof) code only: just like in C, one
cannot compute the length of a buffer at run-time. Therefore, a typical
pattern is to use refinements to tie together a buffer and its length, as we
saw with the initial ``memcpy`` example.

.. code:: fstar

    let do_something (x: B.buffer UInt64.t) (l: U32.t { U32.v l = B.length x }): St unit =
      ()

**Allocating a buffer on the stack** is done using the ``alloca`` function,
which takes an initial value and a length. ``alloca`` requires that the top
of the stack be a valid stack frame.

.. code:: fstar

    let test_alloc_stack (): Stack unit (fun _ -> True) (fun _ _ _ -> True) =
      push_frame ();
      let b = B.alloca 0UL 8ul in
      pop_frame ();
      ()

**Allocating a buffer on the heap** is done using the ``malloc`` function,
which takes a region, an initial value and a length. The region is purely
for proof and separation purposes, and has no effect on the generated code. A
buffer created with ``malloc`` can be freed with ``free``.

.. code:: fstar

    let test_alloc (): St unit =
      let b = B.malloc HS.root 0UL 8ul in
      B.free b

**Pointer arithmetic** is performed by the means of the ``sub`` function. Under
the hood, the ``sub`` function returns a buffer that points to the same
underlying reference, but has different ``idx`` and ``length`` fields.

.. code:: fstar

    let test_sub (): St unit =
      let b = B.malloc HS.root 0UL 8ul in
      let b_l = B.sub b 0ul 4ul in // idx = 0; length = 4
      let b_r = B.sub b 4ul 4ul in // idx = 4; length = 4
      B.free b

Just like in C, one can only free the base pointer, i.e. this is an error:

.. code:: fstar

    [@ expect_failure ]
    let test_sub_error (): St unit =
      let b = B.malloc HS.root 0UL 8ul in
      let b_l = B.sub b 0ul 4ul in // idx = 0; length = 4
      B.free b_l

**Reading and modifying** a buffer is performed by means of the ``index``
and ``upd`` functions. These are exposed as the ``.()`` and ``.()<-``
operators respectively, defined in ``LowStar.BufferOps``. This latter module
module only contains those operators, and is meant to be used with
``open`` to bring operators into scope without further polluting the
context with any definition from ``LowStar.Buffer``.

.. code:: fstar

    let test_index (): St unit =
      let b = B.malloc HS.root 0UL 8ul in
      b.(0ul) <- UInt64.add_mod b.(0ul) b.(0ul);
      B.free b

Buffers are reflected at the proof level using sequences, via the ``as_seq``
function, which returns the contents of a given buffer in a given heap, i.e.
a sequence slice ranging over the interval ``[idx; idx + length)``.

.. code:: fstar

    let test_as_seq (): St unit =
      let b = B.malloc HS.root 0UL 1ul in
      let h = ST.get () in
      assert (Seq.equal (B.as_seq h b) (Seq.cons 0UL Seq.createEmpty));
      B.free b

``B.get`` is an often-convenient shorthand to index the value of a
given buffer in a given heap.

.. code:: fstar

    let test_get (): St unit =
      let b = B.malloc HS.root 0UL 1ul in
      let h = ST.get () in
      assert (B.get h b 0 = 0UL);
      B.free b

**C NULL pointers**

``LowStar.Buffer`` also exposes a model of the C NULL pointer, ``null`` --
this is what you should use if you need zero-length buffers. The NULL
pointer is always live, and always has length 0. The ``pointer`` and
``pointer_or_null`` functions define convenient aliases, while the ``(!*)``
operator (defined in ``LowStar.BufferOps``) guarantees that the dereference
will be pretty-printed with a ``*`` C dereference, as opposed to an access
at array index 0. Pointers can always be tested for nullity via the
``is_null p`` function, which is guaranteed to be pretty-printed as ``p !=
NULL``.

.. _modifies-library:

The modifies clauses library
----------------------------

The current heap model of F* is based on a select-update theory: the heap is
reflected as a map, allocation adds a key in the map, assignment updates the
map, and reading selects from the map.

Proving properties of programs therefore requires the programmer to reason about
the heap model. However, stating precise post-conditions that refer to a
particular heap after a particular update does not scale up to large programs:
we want to reason *abstractly* about modifications, and use a library of
*composable* predicates that allow one to *generically* reason about a given
modification to the heap.

This is where the ``LowStar.Modifies`` library comes in handy. The modifies
clauses library allows one to reason about allocation, de-allocation,
modifications using a single unified ``modifies`` clause. An abstract notion of
a memory location allows composing predicates, and deriving properties such as:
"if I modify a location ``l1`` disjoint from ``l2``, then the contents of the
memory at address ``l2`` remain unchanged".

**Abstract memory locations**

The ``LowStar.Modifies`` library abstracts over memory locations. Memory
locations have type ``loc``. Locations form a monoid, where ``loc_none`` is
the empty location and ``loc_union`` combines two location to form the union of
the two.

Several injections exist to create locations; for now, we will mostly use
``loc_buffer``, which injects a ``LowStar.Buffer.t`` into an abstract location.

**Inclusion and disjointness**

The ``LowStar.Modifies`` module provides an inclusion relation, via
``loc_includes``. This allows the programmer to state, for instance, that the
location of a stack-allocated buffer is included in its stack frame.

Perhaps more useful is the ``loc_disjoint`` predicates, which allows the
programmer to state that two memory locations do not overlap.

**The modifies clause**

The modifies clause is of the form ``modifies l h0 h1`` where ``l`` is an
abstract memory location, ``h0`` is the initial heap and ``h1`` is the
resulting heap. Here is an example:

.. code:: fstar

    module M = LowStar.Modifies

    let example_modifies_callee (b1 b2: B.buffer UInt32.t) : Stack unit
      (requires (fun h -> B.live h b1 /\ B.live h b2 /\ B.length b1 == 1 /\ B.length b2 == 1 /\ B.disjoint b1 b2))
      (ensures (fun h _ h' ->
        M.modifies (M.loc_union (M.loc_buffer b1) (M.loc_buffer b2)) h h' /\
        B.live h' b1 /\ B.live h' b2 /\
        B.get h' b1 0 == 18ul /\ B.get h' b2 0 == 42ul
      ))
    = b2.(0ul) <- 42ul;
      b1.(0ul) <- 18ul

The pre- and post-conditions of the ``example_modifies_callee``
function state that, if ``b1`` and ``b2`` are two disjoint live
buffers of length 1, then ``example_modifies`` changes their
contents to 18ul and 42ul, respectively. In itself, the modifies
clause tells nothing, but it starts becoming useful when the
``example_modifies_callee`` function is called by another
function:

.. code:: fstar

    let example_modifies_caller (b0: B.buffer UInt32.t) : Stack unit
      (requires (fun h -> B.live h b0 /\ B.length b0 == 3))
      (ensures (fun h _ h' ->
        M.modifies (M.loc_buffer b0) h h' /\
        B.live h' b0 /\
        B.get h' b0 0 == B.get h b0 0
      ))
    = let b1 = B.sub b0 1ul 1ul in
      let b2 = B.sub b0 2ul 1ul in
      example_modifies_callee b1 b2;
      assert (forall h . B.get h b0 0 == B.get h (B.gsub b0 0ul 1ul) 0)

This function takes a buffer ``b0`` of length 3, and from it,
extracts two disjoint buffers, ``b1`` and ``b2``, as the
sub-buffers of ``b0`` of length 1 at offsets 1 and 2,
respectively. Since they are both live and disjoint, they can then
be passed to ``example_modifies_callee``. Then, the post-condition
of ``example_modifies_caller`` about the contents of the cell of
``b0`` at offset 0 is due to the fact that that cell of ``b0`` is
disjoint from both ``b1`` and ``b2`` (because it is the cell of
the sub-buffer of ``b0`` at offset 0, as suggested by the
``assert``), and so, by virtue of the ``modifies`` clause of
``example_modifies_callee``, its value is preserved.
