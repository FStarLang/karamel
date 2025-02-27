(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

type include_ = All | InternalOnly of string | HeaderOnly of string | COnly of string

type compiler_flavor =
  | Generic
  | GCC
  | Clang
  | Compcert
  | MSVC

let string_of_compiler_flavor = function
  | Generic -> "generic"
  | GCC -> "gcc"
  | Clang -> "clang"
  | Compcert -> "compcert"
  | MSVC -> "msvc"

let compiler_flavor_of_string = function
  | "generic" -> Generic
  | "gcc" -> GCC
  | "clang" -> Clang
  | "compcert" -> Compcert
  | "msvc" -> MSVC
  | s -> failwith ("unrecognized compiler flavor: " ^ s)

let pinc b = function
  | All -> Buffer.add_string b "*"
  | InternalOnly h
  | HeaderOnly h -> Buffer.add_string b h; Buffer.add_string b ".h"
  | COnly h -> Buffer.add_string b h; Buffer.add_string b ".c"

(** Some of these will be filled by [Driver].  *)
let no_prefix: Bundle.pat list ref = ref Bundle.[
  Module [ "C" ];
  Module [ "C"; "Compat" ];
  Module [ "C"; "Endianness" ];
  Module [ "C"; "Compat"; "Endianness" ];
  Module [ "LowStar"; "Endianness" ]
]
let fstar = ref "fstar.exe" (* F* command to use *)
(* krmllib.h now added directly in Output.ml so that it appears before the first
 * #ifdef *)
let add_include: (include_ * string) list ref = ref [ ]
let add_include_tmh = ref false
let add_early_include: (include_ * string) list ref = ref [ ]
let warn_error = ref "+1@2@3+4..8@9+10@11+12..18@19+20..22+24..25@26..28"
let tmpdir = ref "."
let includes: string list ref = ref []
let verbose = ref false
let silent = ref false
let exe_name = ref ""
let cc = ref ""
let cc_flavor : compiler_flavor option ref = ref None
let m32 = ref false
let fsopts: string list ref = ref []
let ccopts: string list ref = ref []
let ldopts: string list ref = ref []
(* Note: do not populate this field directly but rather do it in Karamel.ml
 * behind the "Options.minimal" test. *)
let bundle: Bundle.t list ref = ref []
let crates: Bundle.t list ref = ref []
let library: Bundle.pat list ref = ref []
let hand_written: Bundle.pat list ref = ref []
let debug_modules: string list ref = ref []
let debug s = List.exists ((=) s) !debug_modules

type backend = C | Rust | Wasm
let backend = ref C
let wasm () = !backend = Wasm
let rust () = !backend = Rust
let no_box = ref false
let contained: string list ref = ref []
let keep_tuples = ref false

let static_header: Bundle.pat list ref = ref []
let minimal = ref false
let by_ref: (string list * string) list ref = ref []
let ctypes: Bundle.pat list ref = ref []
let record_renamings = ref false

(* wasm = true ==> these two are false *)
let struct_passing = ref true
let anonymous_unions = ref true

let compound_literals = ref true
let short_enums = ref true
let alloca_if_vla = ref false
let cast_allocations = ref false
let parentheses = ref false
let curly_braces = ref false
let unroll_loops = ref (-1)
let tail_calls = ref false
let no_shadow = ref false
let no_return_else = ref false

(* TODO: remove this *)
type merge = No | Prefix | Aggressive
let merge_variables = ref No

let linux_ints = ref false
let microsoft = ref false
let extern_c = ref false
let short_names = ref true
let cxx_compat = ref false

let extract_uints = ref false
let builtin_uint128 = ref false

let rst_snippets = ref false

let header = ref ""
let c89_std = ref false
let c89_scope = ref false

(* A set of extra command-line arguments one gets for free depending on the
 * detected C compiler. *)
let default_options (k : compiler_flavor) =
  (* Note: the 14.04 versions of Ubuntu rely on the presence of _BSD_SOURCE to
   * enable the macros in endian.h; future versions use _DEFAULT_SOURCE which is
   * enabled by default, it seems, but there are talks of issuing a warning if
   * _BSD_SOURCE is defined and not the newer _DEFAULT_SOURCE... *)
  let gcc_like_options = [|
    "-ccopts";
    "-Wall,-Werror," ^
    "-Wno-unknown-warning-option," ^
    "-g,-fwrapv,-D_BSD_SOURCE,-D_DEFAULT_SOURCE" ^
    (if Sys.os_type = "Win32" then ",-D__USE_MINGW_ANSI_STDIO" else "") ^
    (if !parentheses then "" else ",-Wno-parentheses")
  |] in
  let gcc_options = Array.append gcc_like_options
    [| "-ccopt"; if !c89_std then "-std=c89" else "-std=c11" |]
  in
  match k with
  | GCC | Clang ->
    if !cxx_compat
    then gcc_like_options
    else gcc_options
  | Compcert -> [|
      "-warn-error"; "@6@8";
      "-fnostruct-passing"; "-fnoanonymous-unions";
      "-ccopts"; "-g,-D_BSD_SOURCE,-D_DEFAULT_SOURCE";
    |]
  | MSVC -> [|
      "-warn-error"; "+6"; "-falloca"
    |]
  | Generic -> [| |]

(** Drop is now deprecated and there is not a single situation left that calls
    for it. If you must implement something with macros or static inline (i.e.,
    something that has no external linkage), then it suffices to cover it with
    -library *and* -static-inline. If you must use macros (don't), then [@
    CMacro ] probably will come in handy, too. *)
let drop: Bundle.pat list ref = ref []

(* Use for rust and eurydice *)
let allow_tapps = ref false

(* Rust only: foo_bar_baz.fst gets emitted as foo/bar_baz.fst with depth=1 and
   foo/bar/baz.fst with depth = 2 (you get the idea). *)
let depth = ref 1
