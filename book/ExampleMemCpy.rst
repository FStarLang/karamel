Example: `memcpy`
=================

The snippet below implements a classic ``memcpy`` function, copying ``len``
elements of type ``a`` from ``src`` into ``dst``.

.. literalinclude:: ../test/MemCpy.fst
    :language: fstar

This example showcases several features of Low*. We only present the code from
a high-level point of view.

The code starts by opening several modules that are part of the "Low*
standard library".

- ``Buffer`` is our model of stack- and heap- allocated C arrays
  (described in :ref:`buffer-library`)
- ``Seq`` is the sequence abstraction from the F* standard library, which
  ``Buffer`` uses to reflect the contents of a given buffer in a given heap
  at the proof level
- ``Modifies`` provides a universal modifies clause over buffers, references
  and regions (described in :ref:`modifies-library`)
- ``UInt32`` is a model of the C11 ``uint32_t`` type, reflected at the proof
  level using natural numbers (described in :ref:`machine-integers`)
- ``HyperStack`` is our model of the C memory layout (described in
  :ref:`memory-model`)
- ``C`` and ``C.Loops`` expose some C concepts to F* (described in
  :ref:`c-library`)

The first definition is a lemma over sequences: if two sequences are equal over
the slice ``[0; i)`` and their ``i``\ -th element is equal, then they are equal
over the slice ``[0; i + 1)``. This lemma is required to prove the functional
correctness of ``memcpy``. Lemmas are erased and do not appear in the generated
code, so it is safe to mix lemmas with Low* code.

Next, then ``memcpy`` function is defined and annotated with pre- and
post-conditions, using liveness and disjointness predicates. The post-condition
states that after calling ``memcpy src dst len``, the destination and the source
have the same contents up to index ``len``.

The implementation of ``memcpy`` uses a C-style ``for`` loop with a loop
invariant and a loop body. Alternatively, one could write a recursive function,
relying on the C compiler to hopefully perform tail-call optimization.

Finally, the ``main`` function uses ``push_frame`` and ``pop_frame``, two
combinators from the memory model that indicate that this code conceptually
executes in a new stack frame. In this new stack frame, two test arrays are
allocated on the stack. These are arrays of 64-bit unsigned integers, as denoted
by the ``UL`` Low* suffix for machine integers. The ``memcpy`` function is
called over these two arrays. From a verification perspective, since the stack
frame is freed after calling ``main``, we can successfully state that ``main``
modifies no buffer.
