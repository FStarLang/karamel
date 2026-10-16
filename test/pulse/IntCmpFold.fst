module IntCmpFold

assume
val f : bool -> Dv unit

let main () =
  let open FStar.UInt32 in
  [@@CInline] let x = 1ul in
  [@@CInline] let y = 2ul in
  f (x = y);
  f (x < y);
  f (x <= y);
  f (x > y);
  f (x >= y);
  f (x <> y);
  f (x = x);
  f (x < x);
  f (x <= x);
  ()

(* Same, but signed, and with a negative constant: the comparisons must be
   folded according to the *signed* order. *)
let main_signed () =
  let open FStar.Int32 in
  [@@CInline] let x = (-1l) in
  [@@CInline] let y = 1l in
  f (x = y);
  f (x < y);
  f (x <= y);
  f (x > y);
  f (x >= y);
  f (x <> y);
  f (x = x);
  f (x < x);
  f (x <= x);
  ()

(* The extremal values of every width. The [@@CInline] lets are what keeps F*
   from doing the folding itself, before krml even sees the comparison. *)
let main_uint8 () =
  let open FStar.UInt8 in
  [@@CInline] let x = 0uy in
  [@@CInline] let y = 255uy in
  f (x < y);
  f (y < x);
  ()

let main_int8 () =
  let open FStar.Int8 in
  [@@CInline] let x = (-128y) in
  [@@CInline] let y = 127y in
  f (x < y);
  f (y < x);
  ()

let main_uint16 () =
  let open FStar.UInt16 in
  [@@CInline] let x = 0us in
  [@@CInline] let y = 65535us in
  f (x < y);
  f (y < x);
  ()

let main_int16 () =
  let open FStar.Int16 in
  [@@CInline] let x = (-32768s) in
  [@@CInline] let y = 32767s in
  f (x < y);
  f (y < x);
  ()

let main_uint64 () =
  let open FStar.UInt64 in
  [@@CInline] let x = 0uL in
  [@@CInline] let y = 18446744073709551615uL in
  f (x < y);
  f (y < x);
  ()

(* Note: reading these two as unsigned would flip both answers. *)
let main_int64 () =
  let open FStar.Int64 in
  [@@CInline] let x = (-9223372036854775808L) in
  [@@CInline] let y = 9223372036854775807L in
  f (x < y);
  f (y < x);
  ()

let main_sizet () =
  let open FStar.SizeT in
  [@@CInline] let x = 1sz in
  f (x = x);
  f (x < x);
  ()

(* Nothing to fold here: only one side is a constant. *)
let main_var (z : UInt32.t) =
  let open FStar.UInt32 in
  [@@CInline] let x = 1ul in
  f (x = z);
  f (z < x);
  ()

(* Idem, at a signed type and with a negative constant. *)
let main_var_signed (z : Int32.t) =
  let open FStar.Int32 in
  [@@CInline] let x = (-1l) in
  f (x = z);
  f (z < x);
  ()

(* Idem, at a narrow width, where C would promote both operands to int. *)
let main_var_narrow (z : UInt8.t) =
  let open FStar.UInt8 in
  [@@CInline] let x = 255uy in
  f (x = z);
  f (z < x);
  ()

let cast_prevents_fold () =
  [@@CInline] let x = 1uy in
  [@@CInline] let y = 2us in
  f (FStar.Int.Cast.uint8_to_uint16 x `FStar.UInt16.lt` y)
