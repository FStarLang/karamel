Advanced KreMLin topics
=======================

Bundling
--------

Bundles ``B`` are of the form ``N₁+..+Nₙ=M₁,...,Mₙ``, where ``Nᵢ`` is a module
name and ``Mᵢ`` is a pattern. The ``N₁+..+Nₙ=`` part is optional.

Patterns are namespaces (i.e. a dot-separated list of module names) where the
last module name may be a wildcard ``*``. Examples of valid patterns are ``FStar.*``,
``Hacl.Impl.Ed25519.*``, ``*``. Examples of invalid patterns are the empty
pattern; ``*.Impl`` (wildcard not in trailing position); etc.

.. note::

  Note that ``Hacl.Impl.Chacha20.*`` matches ``Hacl.Impl.Chacha20.Constants``
  but not ``Hacl.Impl.Chacha20`` -- this is unlike F*'s syntax for, say,
  ``--extract`` or ``--using_facts_from``.

Bundles for grouping files together
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The first purpose of bundles is to group F* modules into a single C file. All of
the ``Nᵢ`` and ``Mᵢ`` are concatenated into a C single file. The name of the single
file is ``N₁_..._Mₙ``, but can be controlled by appending an optional
``[rename=FooBar]`` argument to the bundle ``B``.

Bundles for hiding implementation details
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The second purpose of bundles is to hide beneath a C header some internal
declarations that otherwise would've been public following the default F*
visibility rules. Consider, for instance, the following bundle argument taken
from `HACL*'s Makefile <https://github.com/project-everest/hacl-star/blob/25e19b1c906d4de18d9bfe767a1cd9a5fbf6698c/Makefile.common#L96>`_:

.. code-block:: make

  CHACHA20_BUNDLE=-bundle Hacl.Chacha20=Hacl.Impl.Chacha20,Hacl.Impl.Chacha20.*

The ``Hacl.Chacha20`` module only defines a single entry point:
``chacha20_encrypt``, which is exactly the one definition you want to see in
your C header file. Any other definition is an implementation detail, for instance
``Hacl.Impl.Chacha20.Core32.create_st``, and should not appear in a header file
distributed to C clients.

This can be achieved by writing an ``.fsti`` file with ``val chacha20_encrypt``,
leaving everything else to be hidden in its corresponding ``.fst`` file.
This is, however, not feasible, as this would create a single gigantic file
that would be verified sequentially and would take 20 minutes to verify, at
best.

Users therefore want modularity at the level of F*, but want to get rid of the
modularity when going to C.

Bundling, in addition to grouping several F* modules in a single C file,
therefore changes the visibility of declarations (types, functions, externals)
as follows:

- visibility is left as-is for each one of the ``Nᵢ``
- visibility becomes as-needed for each one of the ``Mᵢ``, i.e. the declarations in
  each ``Mᵢ`` become private (i.e. do not appear in the .h) unless otherwise needed

.. note::

  Since KreMLin automatically eliminates unreachable definitions by default,
  bundling oftentimes prunes the call-graph quite heavily and is used to remove
  definitions that would otherwise be unreachable.

Some reasons why some declaration ``d`` in an ``Mᵢ`` might not be kept as private:

- ``d`` is a function that is called from a separate C file, thus requiring an
  externally-visible declaration
- ``d`` is a type that appears in the signature of a public function.


Finally, a finer point of semantics which turns out to be quite useful in
practice: in case an F* module is matched by two patterns, it will appear in the
bundle that matched it first, i.e. bundles follow a left-to-right order.

Examples of bundles
^^^^^^^^^^^^^^^^^^^

Taken from HACL*...

.. code-block:: bash

  -bundle Foo.Bar1= # this is a no-op, Bar1 is kept as-is in its own file
  -bundle Foo.Bar2= # idem
  -bundle Foo.*[rename=Foo_Misc]
    # everything in the Foo namespace EXCEPT for Bar1 and Bar2 goes into
    # Foo_Misc, relying on the left-to-right semantics

Debugging bundles
^^^^^^^^^^^^^^^^^

``-d bundle`` will spew out some debugging info to figure out how F* matched
modules

Oftentimes, one will use ``-bundle`` to get rid of some definitions (e.g.
spec). If a declaration is not eliminated as expected, use ``-d reachability``
which will explain why a declaration is still reachable and, therefore, not
marked as private.

Separate compilation via KreMLin
--------------------------------

This sections covers authoring two different projects that are built, extracted to
C and compiled separately.

Via external linking
^^^^^^^^^^^^^^^^^^^^

The preferred way to achieve separate verification and compilation is by
extracting and compiling projects separately, and linking them together at the
final stage. In essence, each project produces a library (by default, static,
i.e. a ``.a`` file), and clients link against that library.

In particular, this means that if project B (e.g. miTLS) depends on project A
(e.g. HACL*), then:

- project B should assert that project A has already been verified (via
  ``--already_cached``) and compiled to ``liba.a`` (via suitable ``make``
  checks)
- project B must ensure that no linker symbols from project A are generated as
  part of its build (using kremlin's ``-library`` option)
- project B will regenerate headers for declarations from within project A that
  will be used by project A: this is the declaration from B, as seen from
  project A; see as an example ``mitls-fstar/src/tls/dist/compact/EverCrypt.h``

The last point means that project B will *never* include a header that was
generated via the build of project A.

The reason for doing so is related to monomorphization. Since kremlin does not
dump information from project A to project B, project A may contain a copy of,
say, ``K__int32__int32`` (the type of pairs monomorphized to ``int32``). When
compiling project B, however, kremlin does not know that this pair has already
been monomorphized and may generate a second monomorphization of it in project
B, resulting in C name conflicts and compilation errors if you try to mix
headers from the kremlin run of A with the kremlin run of B. *Never mix headers
obtained from different runs of kremlin!*

Via static headers
^^^^^^^^^^^^^^^^^^

Sometimes, for performance reasons, or to avoid compiling and linking ``liba.a``
into project B, users will want to distribute project A (or part of it)
exclusively as a set of static headers, i.e. headers that contain definitions
marked as ``inline static``.

In that case, project A must pass a suitable ``-static-header`` option to
KreMLin (same syntax as ``-bundle``, ``-library``, etc.). Definitions that match
the argument will then appear in their respective header files.

Project B will then need to use (in addition to ``-library``):

- the same ``-static-header`` option as A, to ensure that there is agreement in
  the prototypes generated in B's vision of A and A's actual C file
- ``-add-include``, to include the header from A that contains the static inline
  definitions

.. code-block:: c

  // From A.h
  inline static void A_foo(uint32_t *src) {
    ...
    // code
    ...
  }

  // From B_A.h, i.e. B's prototypes for A's declarations
  inline static void A_foo(uint32_t *src);

This method is potentially more efficient than external linking, but should only
be used for functions whose type signatures do not rely on any monomorphized
type (see digression above).

.. note::

  kremlib does a mix of these two approaches; uint modules are extracted as
  static headers (and the suitable -static-header and -library options for
  clients are hardcoded in kremlin) -- this allows projects such as HACL* to not
  require any libkremlib.a; other parts of kremlib do not use this facility,
  meaning that projects like miTLS still link against libkremlib.a to find
  external symbols (e.g. from ``FStar.Date``)
