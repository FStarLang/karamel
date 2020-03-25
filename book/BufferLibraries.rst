Low* buffer libraries
=====================

In addition to mutable buffers, we provide libraries for immutable buffers,
const pointers and uninitializer buffers.

Immutable buffers
-----------------

Immutable buffers are in ``LowStar.ImmutableBuffer`` and enjoy a ``recall``
axiom that allows bringing into scope the fact that the buffer still has the
same contents as when it was created.

This is particularly useful for top-level constants. There are numerous examples
of this in HACL*. Note that owing to some design choices, immutable buffers do
*NOT* generate a ``const`` pointer in C.

Uninitialized buffers
---------------------

In ``LowStar.UninitializedBuffer``.

Const pointers
--------------

In order to manipulate const pointers, you can use ``LowStar.ConstPointer``. It
is represented as an abstract type distinct from regular, immutable, or unitialized
buffers (all instances of the base monotonic buffer type). Having a separate
abstract type allows identifiying const pointers as a separate, disjoint type at
extraction, without requiring the built-in Low* checker in KreMLin to insert
casts.

Injecting ``buffer`` or ``ibuffer`` into a ``const_buffer`` generates no casts
in C, as the conversion from ``t*`` to ``const t*`` is implicit.

Projecting ``const_buffer`` to either ``buffer`` or ``ibuffer`` generates a
cast.
