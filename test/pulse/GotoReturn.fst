module GotoReturn

(* The value-returning functions in this module are written as nested
   if-then-else and exist to exercise the -goto_for_early_return transformation,
   which rewrites non-tail returns into `goto`. For that to stay observable, the
   branches must NOT be collapsed into a C ternary (?:) by Karamel's
   use_ternary_op simplification, which only fires when every branch is a pure,
   statement-free ("ternary-eligible") expression. We therefore wrap each branch
   value in an opaque (assumed) call: Karamel treats a call to a non-builtin
   function as non-readonly, so the nested if-then-else is lowered to statements
   with early returns that -goto_for_early_return can turn into goto. Using
   assumed vals (no body) also keeps the calls from being inlined or folded away
   by the earlier optimize_lets pass. *)
assume val opaque_int32 (x: Int32.t) : Int32.t
assume val opaque_bool (x: bool) : bool
assume val opaque_uint32 (x: FStar.UInt32.t) : FStar.UInt32.t
assume val opaque_uint64 (x: FStar.UInt64.t) : FStar.UInt64.t
assume val opaque_int64 (x: FStar.Int64.t) : FStar.Int64.t

(* Early return with Int32 *)
let early_return_int (x: Int32.t) : Int32.t =
  if x = 0l then opaque_int32 42l
  else if x = 1l then opaque_int32 43l
  else opaque_int32 44l

(* No early return: single return at the end *)
[@@Comment "This function has no early return.\n  It tests that fline-comments leaves top-level comments unchanged."]
let no_early_return (x: Int32.t) : Int32.t =
  x

(* Early return with two args *)
let early_return_two_args (x: Int32.t) (y: Int32.t) : Int32.t =
  if x = 0l then opaque_int32 42l
  else y

(* Collision avoidance: local named result *)
let collision_test (x: Int32.t) : Int32.t =
  let result = x in
  if result = 0l then opaque_int32 42l
  else if result = 1l then opaque_int32 43l
  else opaque_int32 44l

(* Early return with bool *)
let early_return_bool (x: Int32.t) : bool =
  if x = 0l then opaque_bool true
  else if x = 1l then opaque_bool false
  else opaque_bool true

(* Early return with UInt32 *)
let early_return_uint32 (x: FStar.UInt32.t) : FStar.UInt32.t =
  let open FStar.UInt32 in
  if x = 0ul then opaque_uint32 42ul
  else if x = 1ul then opaque_uint32 43ul
  else opaque_uint32 44ul

(* Early return with UInt64 *)
let early_return_uint64 (x: FStar.UInt64.t) : FStar.UInt64.t =
  let open FStar.UInt64 in
  if x = 0UL then opaque_uint64 42UL
  else if x = 1UL then opaque_uint64 43UL
  else opaque_uint64 44UL

(* Early return with Int64 *)
let early_return_int64 (x: FStar.Int64.t) : FStar.Int64.t =
  let open FStar.Int64 in
  if x = 0L then opaque_int64 42L
  else if x = 1L then opaque_int64 43L
  else opaque_int64 44L

(* Early return with void: use assumed side-effecting function *)
assume val side_effect: Int32.t -> FStar.All.ML unit

let early_return_void (x: Int32.t) : FStar.All.ML unit =
  if x = 0l then side_effect 1l
  else if x = 1l then side_effect 2l
  else side_effect 3l

(* Struct type for testing *)
type point = { px: Int32.t; py: Int32.t }

(* Early return with struct *)
let early_return_struct (x: Int32.t) : point =
  if x = 0l then { px = opaque_int32 1l; py = opaque_int32 2l }
  else if x = 1l then { px = opaque_int32 3l; py = opaque_int32 4l }
  else { px = opaque_int32 5l; py = opaque_int32 6l }

(* Unit/void interaction: returning unit values *)
let unit_return (x: unit) : FStar.All.ML unit =
  if true then x else ()

(* Pulse function with early return *)
open Pulse
#lang-pulse
fn pulse_early_return (x: Int32.t)
  returns r: Int32.t
  ensures pure (x = 0l ==> r = 42l)
  ensures pure (x <> 0l ==> r = 99l)
{
  if (x = 0l) {
    return 42l;
  };
  99l
}

let main () : FStar.All.ML FStar.Int32.t =
  let _ = early_return_int 0l in
  let _ = no_early_return 1l in
  let _ = early_return_two_args 0l 1l in
  let _ = collision_test 2l in
  let _ = early_return_bool 0l in
  let _ = early_return_uint32 0ul in
  let _ = early_return_uint64 0UL in
  let _ = early_return_int64 0L in
  early_return_void 0l;
  let _ = early_return_struct 0l in
  unit_return ();
  let _ = pulse_early_return 0l in
  0l
