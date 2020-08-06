Low* data structure libraries
=============================

Resizable vector
----------------

The ``LowStar.RVector`` module offers a high-level abstraction over regular
mutable buffers that can be resized automatically. This requires the use of a
manually-encoded typeclass of regional elements for reasoning about things being
stored in the vector in case they are allocated.

``LowStar.RVector`` is becoming slightly outdated and does not use the latest
"reference" style for framing and abstract footprints.

Linked list
-----------

See ``kremlib/LowStar.Lib.LinkedList.fst`` and
``kremlib/LowStar.Lib.LinkedList2.fst`` for singly-linked lists. These are
reference modules that use an established, "reference" style for stateful
programming; they are heavily commented and are ready for general-purpose use
except for a few lemmas that could use a judiciously-chosen pattern.

Associative List
----------------

See ``kremlib/LowStar.Lib.AssocList.fst``. Same as above, this is a module
written in a modern style. It demonstrates how to establish a firm abstraction
boundary, and uses ``FStar.Map`` for its functional specification.
