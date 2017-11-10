(** Unified warning handling *)

open Flags
open Ast
open PrintAst

type error = location * raw_error

and raw_error =
  | Dropping of string * error
  | UnboundReference of string
  | BadFrame of string
  | TypeError of string
  | Unsupported of string
  | ExternalError of string
  | ExternalTypeApp of lident
  | Vla of ident
  | LostStatic of string option * lident * string option * lident
  | LostInline of string option * lident * string option * lident
  | MustCallKrmlInit
  | Deprecated of string * string
  | NotLowStar of expr
  | NotWasmCompatible of lident * string

and location =
  string

let locate loc e =
  loc, snd e

let dummy_loc = "unknown"

(** For user-controllable warnings and recoverable errors. *)
exception Error of error
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

(* -------------------------------------------------------------------------- *)

(* The main error printing function. *)

let flags = Array.make 13 CError;;

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
  | _ ->
      (** Things that cannot be silenced! *)
      0
;;

let p_file = function
  | Some file -> file
  | None -> "<no file>"

let rec perr buf (loc, raw_error) =
  (* Now, print an error-specific message. *)
  let p fmt = Printf.bprintf buf ("Warning %d: %s: " ^^ fmt ^^ "\n") (errno_of_error raw_error) loc in
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
      p "Malformed input:\n%s\nIf this function was not meant to be reachable, \
        consider using KreMLin's -d reachability to understand why it is still in \
        your call-graph." e
  | Unsupported e ->
      p "Unsupported: %s" e
  | ExternalError c ->
      p "the following command failed:\n%s" c
  | ExternalTypeApp lid ->
      p "hit a type application of %a, which is not defined; dropping"
        plid lid
  | Vla id ->
      p "%s is a non-constant size, stack-allocated array; this is not supported \
        by CompCert" id
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
        your library MUST MAKE SURE they call kremlinit_globals(); (see \
        kremlinit.c)"
  | NotLowStar e ->
      p "this expression is not Low*; the enclosing function cannot be translated into C*: %a" pexpr e
  | NotWasmCompatible (lid, reason) ->
      p "%a cannot be compiled to wasm (%s)" plid lid reason
  | Deprecated (feature, reason) ->
      p "%s is deprecated\n  %s" feature reason


let maybe_fatal_error error =
  flush stdout;
  flush stderr;
  let errno = errno_of_error (snd error) in
  match flags.(errno) with
  | CError ->
      KPrint.beprintf "%a" perr error;
      failwith "Fatal error"
  | CWarning ->
      KPrint.beprintf "%a" perr error
  | CSilent ->
      ()
;;

let parse_warn_error s =
  let lexbuf = Ulexing.from_utf8_string s in
  let the_parser = MenhirLib.Convert.Simplified.traditional2revised Parser.warn_error_list in
  let user_flags =
    try
      the_parser (fun _ -> Lexer.token lexbuf)
    with Ulexing.Error | Parser.Error ->
      fatal_error "Malformed warn-error list"
  in
  List.iter (fun (f, (l, h)) ->
    if l < 0 || h >= Array.length flags then
      fatal_error "No error for number %d" l;
    for i = l to h do
      flags.(i) <- f
    done;
  ) user_flags
