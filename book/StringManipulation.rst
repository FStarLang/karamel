Low* string manipulation
========================

.. warning::
   The ``C.String`` library is now fully deprecated.

You may freely use string *literals* in your program, of type ``Prims.string``.
This is a valid Low* usage and will not trigger a warning. These strings are
compiled as C literals and as such are zero-terminated.

You may also use non-allocating functions that operate over strings, such as
``FStar.strlen``. All other functions, e.g. ``strcat``, ``substring`` are
non-Low* and will trigger Warning 15, because they perform unchecked
allocations.

Printing strings
----------------

``LowStar.Printf.printf`` is now the official way to print strings. It is entirely
meta-programmed and will meta-evaluate to a series of monomorphic calls, e.g.

.. code:: fstar

  LowStar.Printf.printf "Contents of %xuL -- length: %uL" (l, b) l

will meta-evaluate to:

.. code:: c

  LowStar_Printf_print_string "Contents of ";
  LowStar_Printf_print_buffer_u32(l, b);
  LowStar_Printf_print_string " -- length: ";
  LowStar_Printf_print_u32(l);

There are no plans to make a call to ``LowStar.Printf.printf`` compile to a call
to C's ``printf``.

``LowStar.Printf.sprintf`` generates calls to ``strcat`` *unless* all of your
arguments are constants, in which case the result will entirely meta-evaluate to
a string constant. Use with care and watch out for Warning 15.

String as buffers
-----------------

``LowStar.Literal`` is experimental and needs an overhaul. The idea is to allow
you to cast a string literal as an immutable buffer of ``uint8``. The main issues are:

- no integration with ``LowStar.ConstPointer``, which ``LowStar.Literal`` predates
- since F* imposes that string literals be valid utf8, this means that you can't
  use this as a way to input arbitrary data.

As such, the usefulness of ``LowStar.Literal`` is limited.
