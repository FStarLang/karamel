{ fstar, ocamlPackages, removeReferencesTo, stdenv, symlinks, version, which, z3
}:

stdenv.mkDerivation {
  pname = "karamel";
  inherit version;

  src = ./..;

  outputs = [ "out" "home" ];

  buildInputs = [ fstar removeReferencesTo symlinks which z3 ]
    ++ (with ocamlPackages; [
      ocaml
      dune_3
      findlib
      batteries
      stdint
      ppx_deriving_yojson
      zarith
      pprint
      menhir
      menhirLib
      sedlex
      process
      fix
      wasm
      visitors
      ctypes
    ]);

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

  dontFixup = true;
}
