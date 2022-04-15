open Ocamlbuild_plugin;;

let ctypes_libdir =
  try Sys.getenv "CTYPES_LIB_DIR"
  with Not_found -> failwith "please define CTYPES_LIB_DIR=$(ocamlfind query ctypes)"
in
let krml_home =
  try Sys.getenv "KRML_HOME"
  with Not_found -> failwith "please define KRML_HOME"
in
let cwd = Sys.getcwd () in

(* Names of modules for which Ctypes bindings are required for building the executable *)
let deps = ["Lowlevel"; "Ctypes1"; "Ctypes2"]
in
let flags = List.flatten
    (List.map (fun n ->
         [A"-dllib"; A("-l" ^ n ^ "_c_stubs");
          A"-dllib"; A("-l" ^ n)])
        deps)
in
let dl_flags mode =
  let ext = match mode with
    | "lib" -> !Options.ext_lib
    | "dll" -> !Options.ext_dll
    | _ -> failwith "Invalid flag for linking Ctypes bindings"
  in
  List.flatten
    (List.map (fun n ->
         [("lib/" ^ mode ^ n ^ "_c_stubs")-.-ext;
          (mode ^ n)-.-ext])
        deps)
in

dispatch begin function
| After_rules ->

  (* One can produce C and ML stubs by running the ..._gen.byte program. The
   * source ..._gen.ml has been produced automatically by KaRaMeL but this is
   * irrelevant for the present build description. *)
  rule "cstubs: x_gen_stubs.ml -> x_c_stubs.c, x_stubs.ml"
    ~prods:["lib/%_c_stubs.c"; "lib/%_stubs.ml"]
    ~deps: ["lib_gen/%_gen.byte"]
    (fun env build ->
      Cmd (A(env "./lib_gen/%_gen.byte")));


  (* C files will be compiled by OCamlbuild, then linked into the final
   * executable. This conflicts with the original, KaRaMeL-generated Makefile
   * which also attempts to build these C files... perhaps a hand-written
   * Makefile that does everything at once would be helpful. *)
  flag ["c"; "compile"] & S[A"-I"; A (krml_home / "include")];
  flag ["c"; "compile"] & S[A"-I"; A (krml_home / "krmllib" / "dist" / "minimal")];
  flag ["c"; "compile"] & S[A"-I"; A cwd];

  (* The generator program ..._gen.byte creates a C file that needs to see
   * CTypes headers. *)
  flag ["c"; "compile"; "use_ctypes"] & S[A"-I"; A ctypes_libdir];
  flag ["c"; "compile"; "debug"] & A"-g";

  (* C stubs are now to be found in the lib directory. *)
  flag ["link"] & S[A"-I"; A "lib"];
  flag ["byte"; "link"] & S[A"-dllpath"; A "lib"];

  (* The -lLowlevel flag recursively builds the KaRaMeL-generated C file (the
   * actual library) then links it with the client program. This appears to be
   * dynamic linking. *)
  dep ["ocaml"; "link"; "byte"; "use_stubs"]
    (dl_flags "dll");

  flag ["ocaml"; "link"; "byte"; "use_stubs"] &
    S flags;

  (* For the native program, we are happy with static linking. *)
  dep ["ocaml"; "link"; "native"; "use_stubs"]
    (dl_flags "lib");

| _ -> ()
end
