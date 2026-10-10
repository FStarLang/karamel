module HoistComment

open FStar.HyperStack.ST
open FStar.Int32
open LowStar.Printf

module LC = LowStar.Comment

(* Test hoisting of local variables with interleaved standalone comments.
   After -fhoist-locals, comments should keep their positions relative to
   the declarations they precede. *)

(* All declarations in the declaration zone: comments and declarations
   should appear in the same order with or without -fhoist-locals. *)
let test_decl_zone_comments (): St unit =
  push_frame ();
  LC.comment "MARKER1: before x";
  let x = 1l in
  LC.comment "MARKER2: before y";
  let y = 2l in
  let z = x +^ y in
  printf "test_decl_zone_comments: x=%ld y=%ld z=%ld\n" x y z done;
  pop_frame ()

(* Comment before a declaration that must be separated from its init
   because a real statement precedes it. *)
let test_split_decl_comments (): St unit =
  push_frame ();
  LC.comment "MARKER3: before a";
  let a = 10l in
  printf "a=%ld\n" a done;
  LC.comment "MARKER4: before b";
  let b = 20l in
  let c = a +^ b in
  printf "test_split_decl_comments: b=%ld c=%ld\n" b c done;
  pop_frame ()

(* Several comments and declarations, all in the declaration zone. *)
let test_many_comments (): St unit =
  push_frame ();
  LC.comment "MARKER5: group alpha";
  let p = 1l in
  let q = 2l in
  LC.comment "MARKER6: group beta";
  let r = 3l in
  LC.comment "MARKER7: before s";
  let s = 4l in
  printf "test_many_comments: p=%ld q=%ld r=%ld s=%ld\n" p q r s done;
  pop_frame ()

(* Two consecutive comments before a single declaration: they must not
   be merged or reordered. *)
let test_consecutive_comments (): St unit =
  push_frame ();
  LC.comment "MARKER8: first consecutive";
  LC.comment "MARKER9: second consecutive";
  let v = 42l in
  printf "test_consecutive_comments: v=%ld\n" v done;
  pop_frame ()

(* Consecutive comments before a declaration that gets split because a
   real statement precedes it. *)
let test_consecutive_split (): St unit =
  push_frame ();
  let a = 1l in
  printf "a=%ld\n" a done;
  LC.comment "MARKER10: first after stmt";
  LC.comment "MARKER11: second after stmt";
  let b = 2l in
  printf "test_consecutive_split: b=%ld\n" b done;
  pop_frame ()

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  St C.exit_code
let main argc argv =
  push_frame ();
  test_decl_zone_comments ();
  test_split_decl_comments ();
  test_many_comments ();
  test_consecutive_comments ();
  test_consecutive_split ();
  pop_frame ();
  C.EXIT_SUCCESS
