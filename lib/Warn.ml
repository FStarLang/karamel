(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

(** Unified warning handling *)

open Flags
open PrintAst
open Error

module S = Set.Make(Error)

(* Avoid printing the same warning twice by keeping a set of warnings that have
 * already been emitted *)
let emitted_warnings = ref S.empty

let locate loc e =
  loc, snd e

let dummy_loc = "unknown"

(** For user-controllable warnings and recoverable errors. *)
exception Error of Error.t
exception Fatal of string

let raise_error e =
  raise (Error (dummy_loc, e))

let raise_error_l e =
  raise (Error e)

(** A printf-style routine for printing fatal errors. *)
let fatal_error fmt =
  flush stdout;
  flush stderr;
  Printf.kbprintf (fun buf ->
    Buffer.add_string buf "\n";
    Buffer.output_buffer stderr buf;
    raise (Fatal "Unrecoverable error")
  ) (Buffer.create 16) fmt

let failwith fmt =
  Printf.kbprintf (fun buf -> raise (Fatal (Buffer.contents buf))) (Buffer.create 16) fmt

(* -------------------------------------------------------------------------- *)

(* The main error printing function. *)

let flags = Array.make 28 CError;;

(* When adding a new user-configurable error, there are *several* things to
 * update:
 *   - you should make the array above bigger;
 *   - you should update parsing/options.ml so that the default value is correct
 *     for the new message;
 *)
let errno_of_error = function
  | Dropping _ ->
      1
  | UnboundReference _ ->
      2
  | ExternalError _ ->
      3
  | TypeError _ ->
      4
  | ExternalTypeApp _ ->
      5
  | Vla _ ->
      6
  | LostStatic _ ->
      7
  | LostInline _ ->
      8
  | MustCallKrmlInit ->
      9
  | Deprecated _ ->
      10
  | NotLowStar _ ->
      11
  | NotWasmCompatible _ ->
      12
  | DropDeclaration _ ->
      13
  | NotTailCall _ ->
      14
  | NeedsCompat _ ->
      15
  | Arity _ ->
      16
  | NotInitializerConstant _ ->
      17
  | BundleCollision _ ->
      18
  | IfDef _ ->
      19
  | GeneratesLetBindings _ ->
      20
  | CannotMacro _ ->
      21
  | DropCtypesDeclaration _ ->
      22
  | ConflictMacro _ ->
      23
  | InlineStaticInline _ ->
      24
  | IfDefOnGlobal _ ->
      25
  | NotLowStarCast _ ->
      26
  | LibraryPointerAmbiguity _ ->
      27
  | _ ->
      (** Things that cannot be silenced! *)
      0
;;

let p_file = function
  | Some file -> file
  | None -> "<no file>"

let rec perr buf (loc, raw_error) =
  (* Now, print an error-specific message. *)
  let loc = if loc = "" then "" else Printf.sprintf "%s: " loc in
  let p fmt = Printf.bprintf buf ("Warning %d: %s" ^^ fmt ^^ "\n") (errno_of_error raw_error) loc in
  match raw_error with
  | Dropping (d, e) ->
      p "Not generating code for %s because of the error below:" d;
      Printf.bprintf buf "%a" perr e
  | UnboundReference r ->
      p "Reference to %s has no corresponding implementation; please \
        provide a C implementation"
        r
  | BadFrame f ->
      p "The push/pop frame invariant is broken because:\n  %s" f
  | TypeError e ->
      p "Malformed input:\n%s" e
  | Unsupported e ->
      p "Unsupported: %s" e
  | ExternalError c ->
      p "the following command failed:\n%s" c
  | ExternalTypeApp lid ->
      p "hit a type application of %a, which is not defined; dropping"
        plid lid
  | Vla id ->
      p "%s is a non-constant size, stack-allocated array; this is not supported \
        by CompCert and requires the use of alloca(3) for MSVC" id
  | LostStatic (file1, lid1, file2, lid2) ->
      p "After inlining, %a (going into %s) calls %a (going into %s) -- removing the static qualifier from %a"
        plid lid1 (p_file file1) plid lid2 (p_file file2) plid lid2
  | LostInline (file1, lid1, file2, lid2) ->
      p "After inlining, %a (going into %s) calls %a (going into %s). This is a call across translation units but \
        %a has a C \"inline\" qualifier. The C standard allows removing %a \
        from its translation unit (see C11 6.7.3 §5), and CompCert will do it. %s"
        plid lid1 (p_file file1) plid lid2 (p_file file2) plid lid2 plid lid2
        (if !Options.cc = "compcert" then "Removing the inline qualifier!" else "")
  | MustCallKrmlInit ->
      p "Some globals did not compile to C values and must be initialized \
        before starting main(). You did not provide a main function, so users of \
        your library MUST MAKE SURE they call krmlinit_globals(); (see \
        krmlinit.c). Once you have fixed this, use -warn-error +9 to make this \
        warning non-fatal."
  | NotLowStar e ->
      p "this expression is not Low*; the enclosing function cannot be translated into C*: %a" pexpr e
  | NotWasmCompatible (lid, reason) ->
      p "%a cannot be compiled to wasm (%s)" plid lid reason
  | Deprecated (feature, reason) ->
      p "%s is deprecated\n  %s" feature reason
  | DropDeclaration (lid, file) ->
      p "%a, a monomorphic instance, is first used, and therefore inserted, in \
        file %s which is about to be dropped; you may get a C compiler error about %s \
        if any other module uses this definition"
        plid lid
        file
        Idents.(to_c_identifier (string_of_lident lid))
  | NotTailCall lid ->
      p "%a is recursive but cannot be optimized to a tail-call" plid lid
  | NeedsCompat (lid, reason) ->
      p "%a is not Low*; %s" plid lid reason
  | GeneratesLetBindings (what, e, bs) ->
      p "The translation of %s gives rise to let-bindings, which, once hoisted, \
        would change the evaluation semantics. Rewriting into an if-then-else.\n\
        Offending expression:\n\
        %a\n\
        Offending let-bindings:\n\
        %a" what ppexpr e pplbs bs
  | Arity (lid, reason) ->
      p "Cannot enforce arity at call-site for %a (%s)" plid lid reason
  | NotInitializerConstant (lid, e) ->
      p "The top-level declaration %a, once compiled to a C global variable, \
        generates a static initializer (i.e. run-time code in krmlinit) because \
        its definition is not a C constant; it is:\n  %a" plid lid pexpr e
  | BundleCollision name ->
      p "After bundling, two C files are named %s" name
  | IfDef lid ->
      p "The variable %a cannot be translated as an if-def" plid lid
  | IfDefOnGlobal lid ->
      p "The global %a has a CIfDef attribute -- this will be ignored, use \
        CIfDef only for assume vals" plid lid
  | CannotMacro lid ->
      p "The variable %a cannot be translated as a macro, most likely because it generated a static initializer" plid lid
  | DropCtypesDeclaration (id, faulty_id) ->
     p "Dropping declaration %a from Ctypes bindings because it uses unsupported type %a" plid id plid faulty_id
  | ConflictMacro (lid, macro) ->
     p "%a cannot be compiled to macro %s because another identifier already \
       compiles to the same macro" plid lid macro
  | InlineStaticInline lid ->
      p "%a is marked [@CInline] and also covered by a -static-header krml \
      option... the [@CInline] is redundant because -static-header generates \
      code marked as static inline" plid lid
  | NotLowStarCast e ->
      p "Expression %a is cast to the Top type, which typically indicates code \
      that falls outside of the Low* subset. Please use -dmonomorphization, grep \
      for <: any in the code, and try to rewrite your source code. miTLS \
      relies on this but this is completely unsupported." pexpr e
  | LibraryPointerAmbiguity (lid, e) ->
      p "Top-level constant %a has a pointer type; is made abstract via \
      -library; and its definition is too ambiguous to tell whether it's an \
      array or a pointer. Disabling this warning is unsound. Definition \
      below:\n%a" plid lid pexpr e

let maybe_fatal_error error =
  flush stdout;
  flush stderr;
  let errno = errno_of_error (snd error) in
  match flags.(errno) with
  | CError ->
      KPrint.beprintf "%a" perr error;
      KPrint.beprintf "Warning %d is fatal, exiting.\n" errno;
      exit 255
  | CWarning ->
      if not (S.mem error !emitted_warnings) then begin
        emitted_warnings := S.add error !emitted_warnings;
        KPrint.beprintf "%a" perr error
      end
  | CSilent ->
      ()
;;

let parse_warn_error s =
  let lexbuf = Sedlexing.Utf8.from_string s in
  let the_parser = MenhirLib.Convert.Simplified.traditional2revised KParser.warn_error_list in
  let user_flags =
    try
      the_parser (fun _ -> KLexer.token lexbuf)
    with Sedlexing.MalFormed | Sedlexing.InvalidCodepoint _ | KParser.Error ->
      fatal_error "Malformed warn-error list"
  in
  List.iter (fun (f, (l, h)) ->
    if l < 0 || h >= Array.length flags then
      fatal_error "No error for number %d" l;
    for i = l to h do
      flags.(i) <- f
    done;
  ) user_flags
