open Ocamlbuild_plugin;;

let ctypes_libdir =
  try Sys.getenv "CTYPES_LIB_DIR"
  with Not_found -> failwith "please define CTYPES_LIB_DIR=$(ocamlfind query ctypes)"
in
let kremlin_home =
  try Sys.getenv "KREMLIN_HOME"
  with Not_found -> failwith "please define KREMLIN_HOME"
in
let cwd = Sys.getcwd () in

dispatch begin function
| After_rules ->

  (* One can produce C and ML stubs by running the ..._gen.byte program. The
   * source ..._gen.ml has been produced automatically by KreMLin but this is
   * irrelevant for the present build description. *)
  rule "cstubs: x_gen_stubs.ml -> x_c_stubs.c, x_stubs.ml"
    ~prods:["lib/%_c_stubs.c"; "lib/%_stubs.ml"]
    ~deps: ["lib_gen/%_gen.byte"]
    (fun env build ->
      Cmd (A(env "./lib_gen/%_gen.byte")));


  (* C files will be compiled by OCamlbuild, then linked into the final
   * executable. This conflicts with the original, KreMLin-generated Makefile
   * which also attempts to build these C files... perhaps a hand-written
   * Makefile that does everything at once would be helpful. *)
  flag ["c"; "compile"] & S[A"-I"; A (kremlin_home / "include")];
  flag ["c"; "compile"] & S[A"-I"; A cwd];

  (* The generator program ..._gen.byte creates a C file that needs to see
   * CTypes headers. *)
  flag ["c"; "compile"; "use_ctypes"] & S[A"-I"; A ctypes_libdir];
  flag ["c"; "compile"; "debug"] & A"-g";

  (* C stubs are now to be found in the lib directory. *)
  flag ["link"] & S[A"-I"; A "lib"];
  flag ["byte"; "link"] & S[A"-dllpath"; A "lib"];

  (* The -lLowlevel flag recursively builds the KreMLin-generated C file (the
   * actual library) then links it with the client program. This appears to be
   * dynamic linking. *)
  dep ["ocaml"; "link"; "byte"; "use_stubs"]
    ["lib/dllLowlevel_c_stubs"-.-(!Options.ext_dll);
     "dllLowlevel"-.-(!Options.ext_dll)];
  flag ["ocaml"; "link"; "byte"; "use_stubs"] &
    S[A"-dllib"; A"-lLowlevel_c_stubs";
      A"-dllib"; A"-lLowlevel"];

  (* For the native program, we are happy with static linking. *)
  dep ["ocaml"; "link"; "native"; "use_stubs"]
    ["lib/libLowlevel_c_stubs"-.-(!Options.ext_lib);
     "libLowlevel"-.-(!Options.ext_lib)];

| _ -> ()
end
