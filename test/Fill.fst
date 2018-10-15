module Fill
module B = LowStar.Buffer
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module HST = FStar.HyperStack.ST

let fill_out_uint32
  (b: B.buffer U32.t)
  (len: U32.t)
: HST.Stack unit
  (requires (fun h -> B.live h b /\ U32.v len <= B.length b))
  (ensures (fun h _ h' ->
    B.modifies (B.loc_buffer b) h h'
  ))
= B.fill b 18ul len

let fill_out_uint8
  (b: B.buffer U8.t)
  (len: U32.t)
: HST.Stack unit
  (requires (fun h -> B.live h b /\ U32.v len <= B.length b))
  (ensures (fun h _ h' ->
    B.modifies (B.loc_buffer b) h h'
  ))
= B.fill b 42uy len

let test (_: unit): HST.Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  HST.push_frame ();
  let b1 = B.alloca 1729ul 256ul in
  let b2 = B.alloca 200uy 34ul in
  fill_out_uint32 b1 128ul;
  fill_out_uint8 b2 7ul;
  HST.pop_frame ()

val main: FStar.Int32.t -> B.buffer (B.buffer C.char) ->
  HST.Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  HST.push_frame ();
  test ();
  HST.pop_frame ();
  C.EXIT_SUCCESS
