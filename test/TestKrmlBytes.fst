module TestKrmlBytes

open FStar.Bytes
open FStar.HyperStack.IO

let assert_equal msg (b1 b2: bytes) =
  if not (b1 = b2) then begin
    print_string "Buffers are not equal!!\n";
    print_string msg;
    print_string "\n";
    print_string (print_bytes b1);
    print_string "\n";
    print_string (print_bytes b2);
    print_string "\n";
    C.exit 1l
  end

let main () =
  let test1 = "0102030405060708090a0ffffe" in
  let hex1 = bytes_of_hex test1 in
  assert_equal "#1" hex1 (bytes_of_hex (hex_of_bytes hex1));

  let test1 = "0102030405060708090a0ffffe" in
  let hex1 = bytes_of_hex test1 in
  let test2 = "fffefdfcfbfa" in
  let hex2 = bytes_of_hex test2 in
  let len2 = len hex2 in
  assert_equal "#2" (xor len2 hex2 (xor len2 hex2 hex1)) (slice hex1 0ul len2);

  let hex3 = bytes_of_hex "abcdef" in
  if repr_bytes (int_of_bytes hex3) <> 3 then begin
    print_string "#3 failure\n";
    C.exit 1l
  end;

  let hex3 = bytes_of_hex "01234567" in
  assert_equal "#4" (bytes_of_int 4 (int_of_bytes hex3)) hex3;

  assert_equal "#5" (twobytes (0uy, 1uy)) (bytes_of_hex "0001");

  let hex4 = bytes_of_hex "01234567" in
  let hex4a, hex4b = split hex4 2ul in
  assert_equal "#6a" hex4a (bytes_of_hex "0123");
  assert_equal "#6b" hex4b (bytes_of_hex "4567");

  begin match iutf8_opt (utf8_encode "Napoléon") with
  | None ->
      print_string "#7 utf8 failure\n";
      C.exit 1l
  | Some _ ->
      ()
  end;

  begin match iutf8_opt (bytes_of_hex "c328") with
  | None -> ()
  | _ ->
      print_string "#8 utf8 invalid sequence parsed as valid!\n";
      C.exit 1l
  end;

  0l
