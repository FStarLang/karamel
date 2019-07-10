open Ocamlbuild_plugin

let kremlin_include = (Sys.getenv "KREMLIN_HOME") ^ "/include"
let ctypes_internals = Sys.getenv "CTYPES"

let () =
  dispatch begin function
  | Before_options ->
    Options.use_ocamlfind := true;
    Options.ocaml_pkgs := ["ctypes"; "ctypes.foreign"; "ctypes.stubs"];

    rule "compile %_c_stubs.c" ~prods:["%_c_stubs.o"] ~deps:["%_c_stubs.c"; "%.o"]
      (fun env build ->
         Cmd (S[A"cc";
                A("-I"); A kremlin_include;
                A("-I"); A ctypes_internals;
                A("-I"); A "..";
                A"-c";
                A"-o";
                A(env "%_c_stubs.o");
                A(env "%_c_stubs.c");
               ]));

    rule "compile %.c" ~prods:["%.o"] ~deps:["%.c"]
      (fun env build ->
         Cmd (S[A"cc";
                A("-I"); A kremlin_include;
                A("-I"); A "..";
                A"-c";
                A"-o";
                A(env "%.o");
                A(env "%.c");
               ]));

    rule "gen stubs" ~prods:["%_stubs.ml"; "%_c_stubs.c"] ~deps:["%_gen_stubs.native"]
      (fun env build ->
         let gen_stubs = env "%_gen_stubs.native" in
         Cmd (S[A("./" ^ gen_stubs)]));

  | Before_rules ->
    dep ["file:Client.native"] ["Lowlevel.o"; "Lowlevel_c_stubs.o"; "Lowlevel_bindings.ml"; "Lowlevel_stubs.ml"]

  | _ -> ()
  end

