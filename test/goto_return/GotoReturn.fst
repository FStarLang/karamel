module GotoReturn

(* Early return with Int32 *)
let early_return_int (x: Int32.t) : Int32.t =
  if x = 0l then 42l
  else if x = 1l then 43l
  else 44l

(* No early return: single return at the end *)
let no_early_return (x: Int32.t) : Int32.t =
  x

(* Early return with two args *)
let early_return_two_args (x: Int32.t) (y: Int32.t) : Int32.t =
  if x = 0l then 42l
  else y

(* Collision avoidance: local named result *)
let collision_test (x: Int32.t) : Int32.t =
  let result = x in
  if result = 0l then 42l
  else if result = 1l then 43l
  else 44l

(* Early return with bool *)
let early_return_bool (x: Int32.t) : bool =
  if x = 0l then true
  else if x = 1l then false
  else true

(* Early return with UInt32 *)
let early_return_uint32 (x: FStar.UInt32.t) : FStar.UInt32.t =
  let open FStar.UInt32 in
  if x = 0ul then 42ul
  else if x = 1ul then 43ul
  else 44ul

(* Early return with UInt64 *)
let early_return_uint64 (x: FStar.UInt64.t) : FStar.UInt64.t =
  let open FStar.UInt64 in
  if x = 0UL then 42UL
  else if x = 1UL then 43UL
  else 44UL

(* Early return with Int64 *)
let early_return_int64 (x: FStar.Int64.t) : FStar.Int64.t =
  let open FStar.Int64 in
  if x = 0L then 42L
  else if x = 1L then 43L
  else 44L

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
  if x = 0l then { px = 1l; py = 2l }
  else if x = 1l then { px = 3l; py = 4l }
  else { px = 5l; py = 6l }

(* Unit/void interaction: returning unit values *)
let unit_return (x: unit) : FStar.All.ML unit =
  if true then x else ()

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
  0l
