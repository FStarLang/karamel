open Ocamlbuild_plugin;;

let ctypes_libdir =
  try Sys.getenv "CTYPES_LIB_DIR"
  with Not_found -> failwith "please define CTYPES_LIB_DIR=$(ocamlfind query ctypes)"
in
let kremlin_home =
  try Sys.getenv "KREMLIN_HOME"
  with Not_found -> failwith "please define KREMLIN_HOME"
in

dispatch begin function
| After_rules ->

  (* Producing the C and ML stub files from the kremlin-generated generator
   * program. *)
  rule "cstubs: x_gen_stubs.ml -> x_c_stubs.c, x_stubs.ml"
    ~prods:["%_c_stubs.c"; "%_stubs.ml"]
    ~deps: ["%_gen.byte"]
    (fun env build ->
      Cmd (A(env "./%_gen.byte")));

  (* This is fairly coarse but ensures that the .h gets copied into the _build
   * directory. *)
  dep ["c"; "compile" ] ["Lowlevel.h"];
  flag ["c"; "compile"] & S[A"-I"; A (kremlin_home / "include")];

  (* Linking cstubs *)
  flag ["c"; "compile"; "use_ctypes"] & S[A"-I"; A ctypes_libdir];
  flag ["c"; "compile"; "debug"] & A"-g";

  (* Bytecode stubs link against the dynamic library. *)
  dep ["ocaml"; "link"; "byte"; "use_stubs"]
    ["dllLowlevel_c_stubs"-.-(!Options.ext_dll);
     "dllLowlevel"-.-(!Options.ext_dll)];
  flag ["ocaml"; "link"; "byte"; "use_stubs"] &
    S[A"-dllib"; A"-lLowlevel_c_stubs";
      A"-dllib"; A"-lLowlevel"];

  (* Native stubs link statically against client. *)
  dep ["ocaml"; "link"; "native"; "use_stubs"]
    ["libLowlevel_c_stubs"-.-(!Options.ext_lib);
     "libLowlevel"-.-(!Options.ext_lib)];

| _ -> ()
end
