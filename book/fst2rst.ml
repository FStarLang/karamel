type state = Rst | Fst

let is_fslit s =
  String.length s >= 3 && String.sub s 0 3 = "///"

let next_state prev s =
  if is_fslit s || prev = Rst && s = "" then
    Rst
  else
    Fst

let fst_prefix = {|
.. code:: fstar
|}

let _ =
  let state = ref Rst in
  set_binary_mode_out stdout true;
  while try
    let s = input_line stdin in
    let next = next_state !state s in
    if !state = Rst && next = Fst then
      print_endline fst_prefix
    else if !state = Fst && next = Rst then
      print_newline ();
    state := next;
    match !state with
    | Rst ->
        if s = "" then
          print_newline ()
        else
          print_endline (String.trim (String.sub s 3 (String.length s - 3)))
    | Fst ->
        print_string "  ";
        print_endline s
    ; ;
    true
  with End_of_file ->
    false
  do () done
