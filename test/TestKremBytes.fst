module TestKremBytes

open FStar.Bytes

let main () =
  if
    let test1 = "0102030405060708090a0ffffe" in
    let hex1 = bytes_of_hex test1 in
    not (hex1 = bytes_of_hex (hex_of_bytes hex1))
  then
    1l
  else if
    let test1 = "0102030405060708090a0ffffe" in
    let hex1 = bytes_of_hex test1 in
    let test2 = "fffefdfcfbfa" in
    let hex2 = bytes_of_hex test2 in
    let len2 = len hex2 in
    not (xor len2 hex2 (xor len2 hex2 hex1) = slice hex1 0ul len2)
  then
    2l
  else if
    let hex3 = bytes_of_hex "abcdef" in
    not (repr_bytes (int_of_bytes hex3) = 3)
  then
    3l
  else if
    let hex3 = bytes_of_hex "01234567" in
    not (bytes_of_int 4 (int_of_bytes hex3) = hex3)
  then
    4l
  else if not (twobytes (0uy, 1uy) = bytes_of_hex "0001") then
    5l
  else if
    let hex4 = bytes_of_hex "01234567" in
    let hex4a, hex4b = split hex4 2ul in
    not (hex4a = bytes_of_hex "0123" && hex4b = bytes_of_hex "4567")
  then
    6l
  else if
    match iutf8_opt (utf8_encode "Napoléon") with None -> true | _ -> false
  then
    7l
  else if
    match iutf8_opt (bytes_of_hex "c328") with None -> false | _ -> true
  then
    8l
  else
    0l
