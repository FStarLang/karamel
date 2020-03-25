.. _c-library:

Low* system libraries
=====================

KreMLin offers primitive support for a variety of C concepts. All new libraries
are in F*'s standard library ("ulib") and are prefixed with ``LowStar``. Older
libraries found in ``kremlin/kremlib`` are being phased out and should not be
used.

Comments
--------

Comments can be attached to a top-level definition using F*'s attribute syntax.

.. code:: fstar

  [@ (Comment "This comment will be carried to C") ]
  let main () = 0l

For inline comments, look at the two special combinators defined by
``LowStar.Comment``.

Failure
-------

In order to abort execution of the program in a way that will always compile in
C (not trivial if you are in expression position!), look at ``LowStar.Failure``
that will rely on either the ``KRML_ABORT`` or ``KRML_EABORT`` macro for
generating C code that compiles.

String literals
---------------

See ``LowStar.Literal`` to convert string literals to immutable, always-live
buffers of uint8. This is only for dealing with literals and does not provide a
general-purpose string manipulation library.

Printing
--------

See ``LowStar.Printf`` for printing output. The ``sprintf`` part is only for ML
code, not for Low*, unless all of the arguments to ``sprintf`` are constants and
can be reduced into a constant string by the F* normalizer.
