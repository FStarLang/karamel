module Strlen

module ST = FStar.HyperStack.ST

open LowStar.Printf

inline_for_extraction noextract
let u8mbstr = "📚" // U+1F4DA (Books Emoji); encoded in utf8 as '\xf0\x9f\x93\x9a'
let _ = assert_norm(String.strlen u8mbstr == 1) // String.strlen returns the number of codepoints

let main (argc:Int32.t) (argv: FStar.Buffer.buffer (FStar.Buffer.buffer C.char)) 
: ST.Stack C.exit_code
  (requires (fun _ -> True))
  (ensures (fun _ _ _ -> True))
= let ex1 = String.strlen u8mbstr in
  let ex2 = normalize_term (String.strlen u8mbstr) in

  if ex1 = ex2 then
    (printf "ex1 = ex2 (correct!)\n" done; C.EXIT_SUCCESS)
  else
    (printf "ex1 <> ex2 (incorrect!)\n" done; C.EXIT_FAILURE)
