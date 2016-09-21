module ML16

// The HyperStack library and friends
open FStar.HyperStack
open FStar.HST
open FStar.Buffer
open FStar.Int32

// Some external functions we expose through the foreign function binding
// mechanism.
open ML16Externals

let test1 (_: unit): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  push_frame ();
  print_int32 (C.rand ());
  pop_frame ()

let test2 (_: unit):
  StackInline (Buffer.buffer Int32.t)
  (requires (fun h0 -> is_stack_region h0.tip))
  (ensures (fun h0 b h1 -> live h1 b /\ Buffer.length b = 2))
=
  let b = Buffer.create 0l 2ul in
  upd b 0ul (C.rand ());
  upd b 1ul (C.rand ());
  b

val main: Int32.t -> buffer (buffer C.char) ->
  Stack Int32.t (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  push_frame ();

  // All computations take place in the current frame.
  print_int32 (
    let seed = 42ul in
    C.srand seed;
    let random_value = C.rand () in
    if random_value >=^ 0l then 1l else 0l);

  // Computations take place in [test1]'s frame.
  test1 ();

  // Computations take place in [main]'s frame.
  let b = test2 () in
  print_int32 (index b 0ul +%^ index b 1ul);

  pop_frame ();
  C.exit_success
