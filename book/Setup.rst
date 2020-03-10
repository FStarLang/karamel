Getting started
===============

For the sake of this tutorial, we use a sample project that provides a toy
implementation of bignum addition in C. The project is located in the kremlin
repository, under the ``book/tutorial`` directory.

The sample project has a minimal specification, a corresponding implementation,
a powerful build system that should cover most common situations and a set of C
tests. In short, we hope that this will set a reference style for all new Low*
projects.

We now describe how to get a working setup -- subsequent sections will take a
deeper look at the code.

Installing the tools
--------------------

We recommend using the `Everest script
<https://github.com/project-everest/everest>`_, if only for its ``z3`` and
``opam`` commands, to make sure you have the exact version of the tools we need.
All of our proofs are intimately tied to a specific version of F*, and if you're
not running the right one, you may have trouble even building F*'s standard
library.

.. code-block:: bash

  $ ./everest z3 opam

Then, you can either install F* and KreMLin yourself, or rely on the Everest
script for that purpose:

.. code-block:: bash

  $ ./everest pull FStar make kremlin make

In any case, remember to export suitable values for the ``FSTAR_HOME`` and
``KREMLIN_HOME`` environment variables once you're done.

Be aware that KreMLin is not at this time compatible with recent versions of
OCaml. See `https://github.com/FStarLang/kremlin/issues/169`_ for the discussion.

We strongly recommend using the `fstar-mode.el
<https://github.com/FStarLang/fstar-mode.el>`_ Emacs plugin for interactive mode
support.

.. note::

  There is an extra customization step which allows querying a Makefile
  to figure out the arguments to pass to F*; please follow instructions at
  `https://github.com/project-everest/mitls-fstar#configuring-emacs-mode`_ -- this
  is used pretty pervasively throughout all of the Everest projects and the
  sample project uses it too.

Directory structure
-------------------

We adopt the following canonical and recommended structure for the toy project.

- ``code``: low-level implementation in Low*, extracts to C
- ``code/c``: hand-written C code (unverified), linked with the extracted Low*
  code
- ``specs``: high-level specifications, extract to OCaml for specs testing
- ``specs/ml``: hand-written OCaml code (unverified), linked with the extracted
  OCaml specifications
- ``obj``: F* and OCaml build artifacts, i.e. whatever is covered by F*'s
  ``--depend`` facility: ``.checked`` files (binary serialized build products
  once a file has been verified), ``.ml`` files (the result of F* extracting to
  OCaml), ``.krml`` files (the result of F* dumping its AST for KreMLin),
  ``.cm*`` files (OCaml build), etc.
- ``hints``: F* hint files, i.e. serialized Z3 unsat-cores that facilitate proof
  replay
- ``dist``: a distribution, i.e. a self-contained set of C files for clients to
  consume and check into their project.
- ``tests``: hand-written C tests to make sure the generated code has a suitable
  API.

This toy project will thus illustrate mixing hand-written and generated ML and C
files, a situation that is fairly common when working in Low*. Of course, your
project might not need such complexity, in which case you should feel free to
simplify.

Build
-----

Build is essential! Running ``make`` is the entry point for any contributor to
your project. A poorly designed build system will generate frustration, angst
and conflict in the project, while a well-ironed and smoothed-out build system
will ensure bliss and happiness. Do not neglect your build system!

Reading, understanding and mastering the build of your project might make all
the difference in the world. This section gives an overview of how we build Low*
projects, followed by a reference Makefile.

Overview of a build
^^^^^^^^^^^^^^^^^^^

We advocate the usage of Makefiles (GNU), mostly because F* supports directly
generating a .depend that will contain all the build rules for you. This is a
well-debugged build system, used everywhere in Everest. It's also easy to use,
in that it only requires GNU make.

From a high-level perspective, the following steps need to happen in order to
sucessfully build a Low* project:

- dependency analysis of all F* source files, generating a ``.depend``
- verify all the source files for this project, generating ``.checked`` files
- extract F* code using those checked files to either ``.krml`` or ``.ml``
- build and link ML code (for specs)
- run KreMLin and generate C code
- dependency analysis for the generated C code
- build C code, generating a C library (more rarely, an executable)
- build C tests and link against compiled library.

To limit the amount of complexity, we only recursively execute ``make`` when a
new dependency analysis needs to be performed. This means that C code
compilation will be a sub-make, but everything is tied together in a single
Makefile. In short, our Makefile has only two stages.

.. note::

  As a point of comparison, the HACL* Makefile has more stages: an initial one
  that runs the Vale tool to generate F* files, a second stage (F* compilation &
  extraction to C), a third stage (compilation of generated C code and ctypes
  bindings generation code), a fourth stage (execution then compilation of the
  generated Ctypes OCaml bindings), and perhaps a few more.

Interestingly enough, F* generates in a single pass enough information in the
``.depend`` to build your F* project, but also (roughly) enough information to
build the resulting extracted OCaml files. This means that we do not need to
rely on ``ocamldep`` to generate a dependency graph for building the extracted
OCaml files.

.. note::

  You could conceivably extract all the ``.ml`` files to a separate directory
  and use an external build tool, e.g. ``dune`` -- this is not covered here

Separate F* builds
^^^^^^^^^^^^^^^^^^

Each project is expected to build its own .checked files; running ``make`` in
``FStar/`` establishes the invariant that all the checked files are up-to-date
w.r.t. their respective source files; similarly, running make in ``kremlin/``
ensures that all the ``kremlib`` (C support libraries) ``.checked`` files are
up-to-date.

Any Low* program will need to refer to both ulib in F* and kremlib in KreMLin.
The client Makefile we provide will therefore *enforce* that all the checked
files for the projects it depends on be up-to-date, and will error out
otherwise.

The rationale is that the client project should not need to know how to build F*
.checked files: there may be magic command-line flags, particular options, and
special rules involved in the production of those checked files (for ulib, there
are). If, say, ``ulib/.cache/LowStar.Comment.fst.checked`` is out-of-date, then
the user needs to rebuild F*.

Reference Makefile
^^^^^^^^^^^^^^^^^^

.. literalinclude:: tutorial/Makefile
    :language: make
