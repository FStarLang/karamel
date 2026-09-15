module StringLit

module IO = FStar.HyperStack.IO

open FStar.HyperStack.ST

let test (x:string): Stack string (fun _ -> true) (fun _ _ _ -> true) =
  strcat "hello " x

let cat (x y:string): Stack string (fun _ -> true) (fun _ _ _ -> true) =
  strcat x y

let test_c_string (): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  // C strings, modeled as zero-terminated, not relying on GC
  C.String.(print !$"hello, world\n")

let main (): Stack Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  // F* strings, unaware of zero-termination, supports concatenation using a
  // conservative GC; HyperIO provides functions in the Stack effect
  IO.print_string (test "jonathan!\n");
  // Generates nice testcases to be run with clang -fsanitize=address...!
  IO.print_string (cat "" "");
  IO.print_string (cat "" "\n");
  IO.print_string (cat "\n" "");
  let test_literal, len = LowStar.Literal.buf_len_of_literal "hello\x00" in
  assert (len = 6ul);
  let zero: UInt8.t = LowStar.ImmutableBuffer.index test_literal 5ul in
  // Non-printable bytes followed by hex-digit characters (#710): C's \x escape
  // is greedy, so a literal emitted as "\x01a" is one byte 0x1a, and "\x0fabc"
  // does not even compile. Check the bytes at run time.
  let lit1, len1 = LowStar.Literal.buf_len_of_literal "\x01a" in
  assert (len1 = 2ul);
  let b0 = LowStar.ImmutableBuffer.index lit1 0ul in
  let b1 = LowStar.ImmutableBuffer.index lit1 1ul in
  let lit2, len2 = LowStar.Literal.buf_len_of_literal "\x0fabc" in
  assert (len2 = 4ul);
  let c0 = LowStar.ImmutableBuffer.index lit2 0ul in
  let c3 = LowStar.ImmutableBuffer.index lit2 3ul in
  // A non-printable byte followed by an octal digit: the escape must be padded
  // to three digits ("\0017"), since "\17" would be a single byte 0x0f.
  let lit3, len3 = LowStar.Literal.buf_len_of_literal "\x017" in
  assert (len3 = 2ul);
  let d0 = LowStar.ImmutableBuffer.index lit3 0ul in
  let d1 = LowStar.ImmutableBuffer.index lit3 1ul in
  if b0 = 0x01uy && b1 = 0x61uy && c0 = 0x0fuy && c3 = 0x63uy &&
     d0 = 0x01uy && d1 = 0x37uy then
    FStar.Int.Cast.Full.uint8_to_int32 zero
  else
    1l
