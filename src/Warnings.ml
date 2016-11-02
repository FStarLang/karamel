(** Unified warning handling *)

open Flags
open Ast
open PrintAst

type error = location * raw_error
  (** TODO: error = location * raw_error *)

and raw_error =
  | Dropping of string * error
  | UnboundReference of string
  | BadFrame of string
  | TypeError of string
  | Unsupported of string
  | ExternalError of string
  | ExternalTypeApp of lident
  | Vla of ident

and location =
  string

let locate loc e =
  loc, snd e

let dummy_loc = "unknown"

(** For user-controllable warnings and recoverable errors. *)
exception Error of error

let raise_error e =
  raise (Error (dummy_loc, e))

let raise_error_l e =
  raise (Error e)

(** A printf-style routine for printing fatal errors. *)
let fatal_error fmt =
  flush stdout;
  flush stderr;
  Printf.kbprintf (fun buf -> failwith (Buffer.contents buf)) (Buffer.create 16) fmt

(* -------------------------------------------------------------------------- *)

(* The main error printing function. *)

let flags = Array.make 7 CError;;

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
  | _ ->
      (** Things that cannot be silenced! *)
      0
;;

let rec perr buf (loc, raw_error) =
  (* Now, print an error-specific message. *)
  let p fmt = Printf.bprintf buf ("Warning %d: %s: " ^^ fmt ^^ "\n") (errno_of_error raw_error) loc in
  match raw_error with
  | Dropping (d, e) ->
      p "Not generating code for file: %s" d;
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
        by CompCert" id

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
