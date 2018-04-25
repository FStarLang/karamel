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

#set-options "--z3rlimit 300"

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

module S = FStar.Seq

let slice_plus_one #a (s1 s2: S.seq a) (i: nat): Lemma
  (requires (
    i < S.length s1 /\
    i < S.length s2 /\
    S.equal (S.slice s1 0 i) (S.slice s2 0 i) /\
    S.index s1 i == S.index s2 i))
  (ensures (
    S.equal (S.slice s1 0 (i + 1)) (S.slice s2 0 (i + 1))))
  [ SMTPat (S.slice s1 0 (i + 1)); SMTPat (S.slice s2 0 (i + 1)) ]
=
  let x = S.index s1 i in
  let s1' = S.append (S.slice s1 0 i) (S.cons x S.createEmpty) in
  let s2' = S.append (S.slice s2 0 i) (S.cons x S.createEmpty) in
  assert (S.equal s1' (S.slice s1 0 (i + 1)));
  assert (S.equal s2' (S.slice s2 0 (i + 1)))

let bufstrcmp b s =
  let h0 = ST.get () in
  push_frame ();
  let h1 = ST.get () in
  let i: pointer U32.t = Buffer.create 0ul 1ul in
  let h2 = ST.get () in
  assert (modifies_0 h1 h2);
  let inv h stopped =
    B.live h i /\ B.live h b /\
    B.modifies_1 i h2 h /\ (
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
      let h = ST.get () in
      assert (
        let i: U32.t = B.get h i 0 in
        forall (j: U32.t). {:pattern (B.get h b (U32.v j)) } U32.lt j i ==>
          B.get h b (U32.v j) = C.String.get s j);
      i.(0ul) <- U32.( i.(0ul) +^ 1ul );
      let h' = ST.get () in
      assert (
        let i: U32.t = B.get h i 0 in
        B.get h' b (U32.v i) = C.String.get s i
      );
      false
    end
  in
  C.Loops.do_while inv body;
  let r = C.String.get s (i.(0ul)) = char_of_uint8 0uy in
  let h3 = ST.get () in
  assert (forall (b: buffer char) (i: nat{ i < B.length b }).
    {:pattern (Seq.index (B.as_seq h3 b) i)}
    Seq.index (B.as_seq h3 b) i == B.get h3 b i);
  assert (forall (s: C.String.t) (i: nat { i < C.String.length s }).
    {:pattern (Seq.index (C.String.v s) i)}
    Seq.index (C.String.v s) i == C.String.get s (U32.uint_to_t i));
  assert (
    let i = U32.v (B.get h3 i 0) in
    (forall (j: nat).
      {:pattern (Seq.index (B.as_seq h3 b) j)}
      j < i ==> Seq.index (B.as_seq h3 b) j == Seq.index (C.String.v s) j)
  );
  assert (
    let i = U32.v (B.get h3 i 0) in
    (forall (j: nat).
      {:pattern (Seq.index (Seq.slice (B.as_seq h3 b) 0 i) j)}
      j < i ==> Seq.index (Seq.slice (B.as_seq h3 b) 0 i) j == Seq.index (Seq.slice (C.String.v s) 0 i) j)
  );
  assert (
    let i = U32.v (B.get h3 i 0) in
    Seq.equal (Seq.slice (B.as_seq h3 b) 0 i) (Seq.slice (C.String.v s) 0 i)
  );
  pop_frame ();
  let h4 = ST.get () in
  lemma_modifies_0_1' i h1 h2 h3;
  modifies_popped_0 h0 h1 h3 h4;
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
    B.length b >= C.String.length s /\
    modifies_1 b h0 h1 /\
    U32.v ret = C.String.length s - 1 /\
    Seq.equal (Seq.slice (B.as_seq h1 b) 0 (U32.v ret)) (Seq.slice (C.String.v s) 0 (U32.v ret))))


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
    U32.v ret <= 10 /\
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
let response_length = 65535

let offset_zero_terminated h (b: buffer char) (i: U32.t):
  Lemma
    (requires (U32.v i < B.length b /\ zero_terminated h b))
    (ensures (U32.v i < B.length b /\ zero_terminated h (B.offset b i)))
    [ SMTPat (zero_terminated h b); SMTPat (B.offset b i) ] =
  ()

inline_for_extraction
let (!$) = C.String.of_literal

val respond: (response: buffer char) -> (payload: buffer char) -> (payloadlen: U32.t) ->
  Stack U32.t
    (requires (fun h0 ->
      B.length payload >= U32.v payloadlen /\
      B.live h0 response /\
      B.live h0 payload /\
      B.disjoint response payload /\
      B.length response > 128 + U32.v payloadlen
    ))
    (ensures (fun h0 n h1 ->
      B.live h1 response /\
      B.live h1 payload /\
      B.disjoint response payload /\
      B.modifies_1 response h0 h1 /\
      U32.v n <= 128 + U32.v payloadlen
    ))

let respond response payload payloadlen =
  let n1 = bufstrcpy response !$"HTTP/1.1 200 OK\r\nConnection: closed\r\nContent-Length:" in
  let response = B.offset response n1 in
  let n2 = print_u32 response payloadlen in
  let response = B.offset response n2 in
  let n3 = bufstrcpy response !$"\r\nContent-Type: text/html; charset=utf-8\r\n\r\n" in
  let response = B.offset response n3 in
  let t = Buffer.blit payload 0ul response 0ul payloadlen in
  U32.(n1 +^ n2 +^ n3 +^ payloadlen)

#set-options "--max_ifuel 0"

let respond_index (response: buffer char): Stack U32.t
  (requires (fun h0 ->
    B.live h0 response /\
    B.length response >= 256))
  (ensures (fun h0 n h1 ->
    B.live h1 response /\
    B.modifies_1 response h0 h1 /\
    U32.v n <= 256)) =
  push_frame ();
  let payload = Buffer.create (char_of_uint8 0uy) 256ul in
  let payloadlen = bufstrcpy payload !$"<html><body>Hello world</body></html>" in
  let n = respond response payload payloadlen in
  pop_frame ();
  n

let respond_stats (response: buffer char) (state: U32.t): Stack U32.t
  (requires (fun h0 ->
    B.live h0 response /\
    B.length response >= 256))
  (ensures (fun h0 n h1 ->
    B.live h1 response /\
    B.modifies_1 response h0 h1 /\
    U32.v n <= 256)) =
  push_frame ();
  let payload = Buffer.create (char_of_uint8 0uy) 256ul in
  let n1 = bufstrcpy payload !$"<html>State = " in
  let next = B.offset payload n1 in
  let n2 = print_u32 next state in
  let next = B.offset next n2 in
  let n3 = bufstrcpy next !$"</html>" in
  let n = respond response payload U32.(n1+^n2+^n3) in
  pop_frame ();
  n

let respond_404 (response: buffer char): Stack U32.t
  (requires (fun h0 ->
    B.live h0 response /\
    B.length response >= 512))
  (ensures (fun h0 n h1 ->
    B.live h1 response /\
    B.modifies_1 response h0 h1 /\
    U32.v n <= 512)) =
  push_frame ();
  let payload = Buffer.create (char_of_uint8 0uy) 256ul in
  let payloadlen = bufstrcpy payload !$"<html>Page not found</html>" in
  let n1 = bufstrcpy response !$"HTTP/1.1 404 Not Found\r\nConnection: closed\r\nContent-Length:" in
  let response = B.offset response n1 in
  let n2 = print_u32 response payloadlen in
  let response = B.offset response n2 in
  let n3 = bufstrcpy response !$"\r\nContent-Type: text/html; charset=utf-8\r\n\r\n" in
  let response = B.offset response n3 in
  let t = Buffer.blit payload 0ul response 0ul payloadlen in
  let n = U32.(n1+^n2+^n3+^payloadlen) in
  pop_frame ();
  n

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
    if not (bufstrcmp request !$"GET ") then
      let n = bufstrcpy response !$"error" in
      n

    else
      // Bug of mine here: I was advancing by 5 instead of 4...!
      let request = Buffer.offset request 4ul in

      if bufstrcmp request !$"/ " then
        respond_index response

      else if bufstrcmp request !$"/stats " then
        respond_stats response state.(0ul)

      else
        respond_404 response
  in

  pop_frame ();

  n
