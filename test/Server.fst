module Server

module B = FStar.Buffer
module U32 = FStar.UInt32

open C
open FStar.Buffer
open FStar.HyperStack.ST

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

type pointer t =
  b:B.buffer t { B.length b = 1 }

type server_state =
  pointer U32.t

let zero_terminated (h: HS.mem) (b: B.buffer char) =
  let s = B.as_seq h b in
  B.length b > 0 /\
  B.length b <= FStar.UInt.max_int 32 /\
  uint8_of_char (Seq.index s (B.length b - 1)) = 0uy

#set-options "--z3rlimit 200"

(**
  @summary: compares `b` and `s` for equality (without `s`'s trailing zero)
  @type: true
*)
val bufstrcmp (b: buffer char) (s: C.String.t): Stack bool
  (requires (fun h ->
    B.live h b /\
    C.String.zero_free s /\
    zero_terminated h b))
  (ensures (fun h0 ret h1 ->
    B.live h1 b /\
    modifies_0 h0 h1 /\
    (ret = true ==> (
      let l = C.String.length s in
      B.length b >= l /\ (
      let b = B.as_seq h1 b in
      let s = C.String.v s in
      Seq.length b >= l /\
      Seq.equal (Seq.slice b 0 (l - 1)) (Seq.slice s 0 (l - 1)))))))
let bufstrcmp b s =
  let h0 = ST.get () in
  push_frame ();
  let i: pointer U32.t = Buffer.create 0ul 1ul in
  let h1 = ST.get () in
  let inv h stopped =
    B.live h i /\ B.live h b /\
    B.modifies_1 i h1 h /\ (
    let i: U32.t = B.get h i 0 in
    U32.v i < B.length b /\ U32.v i < C.String.length s /\
    (forall (j: U32.t). {:pattern (B.get h b (U32.v j)) } U32.lt j i ==>
      B.get h b (U32.v j) = C.String.get s j) /\
    (if stopped then
      C.String.get s i = char_of_uint8 0uy \/ C.String.get s i <> B.get h b (U32.v i)
    else
      True))
  in
  let body (): Stack bool
    (requires (fun h -> inv h false))
    (ensures (fun h1 b h2 -> inv h1 false /\ inv h2 b))
  =
    let cb = b.(i.(0ul)) in
    let cs = C.String.get s i.(0ul) in
    if cb <> cs || cs = char_of_uint8 0uy then
      true
    else begin
      i.(0ul) <- U32.( i.(0ul) +^ 1ul );
      false
    end
  in
  C.Loops.do_while inv body;
  let r = C.String.get s 0ul = char_of_uint8 0uy in
  let h2 = ST.get () in
  assert (modifies_1 i h1 h2);
  // assert (r ==> U32.v (B.get h i 0) = C.String.length s - 1);
  // assert (forall (b: buffer char) (i: nat{ i < B.length b }).
  //   {:pattern (Seq.index (B.as_seq h b) i)}
  //   Seq.index (B.as_seq h b) i == B.get h b i);
  pop_frame ();
  let h3 = ST.get () in
  r


(**
  @summary: writes out the contents of `s` up to its trailing zero (excluded) into `b`
  @returns: the number of bytes written out in `b`
  @type: true
*)
assume val bufstrcpy (b: buffer char) (s: C.String.t): Stack U32.t
  (requires (fun h ->
    B.live h b /\
    C.String.zero_free s /\
    B.length b >= C.String.length s - 1))
  (ensures (fun h0 ret h1 ->
    B.live h1 b /\
    B.length b >= C.String.length s - 1 /\
    modifies_1 b h0 h1 /\
    U32.v ret = C.String.length s /\
    Seq.equal (Seq.slice (B.as_seq h1 b) 0 (U32.v ret - 1)) (Seq.slice (C.String.v s) 0 (U32.v ret - 1))))


(**
  @summary: prints the given number in decimal format in the destination buffer
  @returns: the number of bytes written out in `dst`
  @type: true
*)
assume val print_u32 (dst: buffer char) (i: U32.t): Stack U32.t
  (requires (fun h ->
    B.live h dst /\ B.length dst >= 10))
  (ensures (fun h0 ret h1 ->
    modifies_1 dst h0 h1 /\
    U32.v ret <= B.length dst /\
    B.live h1 dst))


(**
  @summary: writes out the contents of `b2` up to its trailing zero (excluded) into `b1`
  @returns: the number of bytes written out in `b1`
  @type: true
*)
assume val bufcpy (b1 b2: buffer char): Stack U32.t
  (requires (fun h ->
    B.live h b1 /\ B.live h b2 /\
    zero_terminated h b2 /\
    B.length b1 >= B.length b2 - 1))
  (ensures (fun h0 ret h1 ->
    B.live h1 b1 /\ B.live h1 b2 /\
    zero_terminated h1 b2 /\
    B.length b2 >= B.length b1 - 1 /\
    modifies_1 b1 h0 h1 /\ (
    U32.v ret < B.length b1 /\
    Seq.equal (Seq.slice (B.as_seq h1 b1) 0 (U32.v ret)) (Seq.slice (B.as_seq h1 b2) 0 (U32.v ret)))))


(** The length that our caller has allocated for us in the destination buffer. *)
unfold
let response_length = 2048

let offset_zero_terminated h (b: buffer char) (i: U32.t):
  Lemma
    (requires (U32.v i < B.length b /\ zero_terminated h b))
    (ensures (U32.v i < B.length b /\ zero_terminated h (B.offset b i)))
    [ SMTPat (zero_terminated h b); SMTPat (B.offset b i) ] =
  ()


(**
  @summary: a demo server
  @type: true

  This is just to demonstrate some low-level style programming along with
  manipulation of strings.
*)
val server (state: server_state) (request response: buffer char):
  Stack U32.t
    (requires (fun h ->
      B.live h state /\ B.live h request /\ B.live h response /\
      B.disjoint state request /\ B.disjoint state response /\
      B.disjoint request response /\
      zero_terminated h request /\
      B.length response = response_length))
    (ensures (fun h0 _ h1 ->
      B.live h1 state /\ B.live h1 request /\ B.live h1 response))
let server state request response =
  push_frame ();

  // Note: need to use the special operator +%^ (wraparound). Otherwise, we'd
  // have to show that there's no overflow.
  U32.(state.(0ul) <- state.(0ul) +%^ 1ul);

  // Assert that the request starts with "GET " (note the space). That way, we
  // learn that the request is at least five characters long.
  let n =
    if not (bufstrcmp request (C.String.of_literal "GET ")) then
      let n = bufstrcpy response (C.String.of_literal "error") in
      n

    else
      let request = Buffer.offset request 4ul in
      let h = ST.get () in
      assert (zero_terminated h request);

      if bufstrcmp request (C.String.of_literal "/\r\n") then
        let n = bufstrcpy response (C.String.of_literal "<html>Hello</html>") in
        n

      else if bufstrcmp request (C.String.of_literal "/stats\r\n") then
        let n1 = bufstrcpy response (C.String.of_literal "<html>State = ") in
        let response = B.offset response n1 in
        let n2 = print_u32 response state.(0ul) in
        let response = B.offset response n2 in
        let n3 = bufstrcpy response (C.String.of_literal "</html>") in
        U32.(n1+^n2+^n3)

      else
        let n = bufstrcpy response (C.String.of_literal "<html>not found</html>") in
        n
  in

  pop_frame ();

  n
