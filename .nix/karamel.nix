{
  fstar,
  ocamlPackages,
  removeReferencesTo,
  stdenv,
  symlinks,
  version,
  which,
  z3,
}: let
  pname = "karamel";
  propagatedBuildInputs = with ocamlPackages; [
    batteries
    stdint
    ppx_deriving_yojson
    zarith
    pprint
    menhirLib
    sedlex
    process
    fix
    wasm
    ctypes
    visitors
    uucp
  ];
  nativeBuildInputs = [fstar removeReferencesTo symlinks which z3] ++ (with ocamlPackages; [ocaml dune_3 findlib menhir]);
in
  stdenv.mkDerivation {
    inherit version pname propagatedBuildInputs nativeBuildInputs;

    src = ./..;

    outputs = ["out" "home"];

    FSTAR_HOME = fstar;
    GIT_REV = version;

    configurePhase = "export KRML_HOME=$(pwd)";

    enableParallelBuilding = true;

    preBuild = "mkdir -p krmllib/hints";

    preInstall = "export PREFIX=$out";
    postInstall = ''
      # OCaml leaves its full store path in produced binaries
      # Thus we remove every reference to it
      for binary in $out/bin/*
      do
        remove-references-to -t '${ocamlPackages.ocaml}' $binary
      done

      symlinks -c $KRML_HOME
      cp -r ./. $home
    '';

    passthru = {
      lib = ocamlPackages.buildDunePackage {
        GIT_REV = version;
        # the Makefile expects `FSTAR_HOME` to be or `fstar.exe` to be
        # in PATH, but this is not useful for buulding the library
        FSTAR_HOME = "dummy";
        inherit version propagatedBuildInputs;
        nativeBuildInputs = with ocamlPackages; [menhir];
        pname = "krml";
        preBuild = ''
          # the library is named `krml` rather than `karamel`
          mv karamel.opam krml.opam
          sed -i '/name krml/a (public_name krml)' lib/dune
          make lib/Version.ml lib/AutoConfig.ml
        '';
        src = ../.;
      };
    };

    dontFixup = true;
  }
