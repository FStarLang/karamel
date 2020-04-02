(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

(** Some of these will be filled by [Driver].  *)
let no_prefix: Bundle.pat list ref = ref Bundle.[
  Module [ "C" ];
  Module [ "C"; "Compat" ];
  Module [ "C"; "Endianness" ];
  Module [ "C"; "Compat"; "Endianness" ];
  Module [ "LowStar"; "Endianness" ]
]
(* kremlib.h now added directly in Output.ml so that it appears before the first
 * #ifdef *)
let add_include: (string option * string) list ref = ref [ ]
let add_include_tmh = ref false
let add_early_include: (string option * string) list ref = ref [ ]
let warn_error = ref "+1..2@3+4..8@9+10@11+12..18@19+20..22"
let tmpdir = ref "."
let includes: string list ref = ref []
let verbose = ref false
let silent = ref false
let exe_name = ref ""
let cc = ref "gcc"
let m32 = ref false
let fsopts: string list ref = ref []
let ccopts: string list ref = ref []
let ldopts: string list ref = ref []
(* Note: do not populate this field directly but rather do it in Kremlin.ml
 * behind the "Options.minimal" test. *)
let bundle: Bundle.t list ref = ref []
let library: Bundle.pat list ref = ref []
let debug_modules: string list ref = ref []
let debug s = List.exists ((=) s) !debug_modules
let wasm = ref false
let static_header: Bundle.pat list ref = ref []
let minimal = ref false
let by_ref: (string list * string) list ref = ref []
let ctypes: Bundle.pat list ref = ref []

(* wasm = true ==> these two are false *)
let struct_passing = ref true
let anonymous_unions = ref true

let compound_literals = ref true
let short_enums = ref true
let alloca_if_vla = ref false
let parentheses = ref false
let curly_braces = ref false
let unroll_loops = ref (-1)
let tail_calls = ref false
let no_shadow = ref false
let no_return_else = ref false
type merge = No | Prefix | Aggressive
let merge_variables = ref No
let linux_ints = ref false
let microsoft = ref false

let extract_uints = ref false
let builtin_uint128 = ref false

let rst_snippets = ref false

let header = ref ""
let c89_std = ref false
let c89_scope = ref false

(* A set of extra command-line arguments one gets for free depending on the
 * value of -cc *)
let default_options () =
  (* Note: the 14.04 versions of Ubuntu rely on the presence of _BSD_SOURCE to
   * enable the macros in endian.h; future versions use _DEFAULT_SOURCE which is
   * enabled by default, it seems, but there are talks of issuing a warning if
   * _BSD_SOURCE is defined and not the newer _DEFAULT_SOURCE... *)
  let gcc_like_options = [|
    "-ccopts";
    "-Wall,-Werror,-Wno-unused-variable," ^
    "-Wno-unknown-warning-option,-Wno-unused-but-set-variable," ^
    "-g,-fwrapv,-D_BSD_SOURCE,-D_DEFAULT_SOURCE" ^
    (if Sys.os_type = "Win32" then ",-D__USE_MINGW_ANSI_STDIO" else "") ^
    (if !parentheses then "" else ",-Wno-parentheses")
  |] in
  let gcc_options = Array.append gcc_like_options
    [| "-ccopt"; if !c89_std then "-std=c89" else "-std=c11" |]
  in
  [
    "gcc", gcc_options;
    "clang", gcc_options;
    "g++", gcc_like_options;
    "compcert", [|
      "-warn-error"; "@6@8";
      "-fnostruct-passing"; "-fnoanonymous-unions";
      "-ccopts"; "-g,-D_BSD_SOURCE,-D_DEFAULT_SOURCE";
    |];
    "msvc", [|
      "-warn-error"; "+6"; "-falloca"
    |];
    "", [| |]
  ]


(** Drop is now deprecated and should be used as a last resort. The only reason
 * now to use drop is if whatever definitions are in this module are NOT
 * implemented with external linkage (static inline, macros). *)
let drop: Bundle.pat list ref = ref []
