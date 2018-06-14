module ML16

// The HyperStack library and friends
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
open FStar.Int32

module HS = FStar.HyperStack

module I32 = FStar.Int32

// Some external functions we expose through the foreign function binding
// mechanism.
open ML16Externals

let test1 (_: unit): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  push_frame ();
  let b = Buffer.create 21l 2ul in
  print_int32 (FStar.Int32.add (index b 0ul) (index b 1ul));
  pop_frame ()

let test2 (_: unit):
  StackInline (Buffer.buffer Int32.t)
  (requires (fun h0 -> is_stack_region (HS.get_tip h0)))
  (ensures (fun h0 b h1 -> live h1 b /\ Buffer.length b = 2))
=
  let b = Buffer.create 0l 2ul in
  upd b 0ul (C.rand ());
  upd b 1ul (C.rand ());
  b

val main: Int32.t -> buffer (buffer C.char) ->
  Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)
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

  let a = index b 0ul in
  let b = index b 1ul in

  assume (FStar.Int.size ((I32.v a) + (I32.v b)) 32); // What to do here, Tej says we shouldn't/can't have add_mod anymore.
  print_int32 (I32.add a b);

  pop_frame ();
  C.EXIT_SUCCESS
