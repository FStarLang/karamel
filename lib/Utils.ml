let try_finally f h = let result =
    try
      f ()
    with e ->
      h ();
      raise e
  in
  h ();
  result

let with_open_in file_path f =
  let c = open_in_bin file_path in
  try_finally (fun () ->
    f c
  ) (fun () ->
    close_in c
  )

let with_open_out_bin file_path f =
  let c = open_out_bin file_path in
  try_finally (fun () ->
    f c
  ) (fun () ->
    close_out c
  )


let cp dst src = with_open_out_bin dst (fun oc ->
  with_open_in src (fun ic ->
    let buf = Bytes.create 2048 in
    while
      let l = input ic buf 0 2048 in
      if l > 0 then begin
        output oc buf 0 l;
        true
      end else
        false
    do () done
  ))


let read ic =
  let buf = Buffer.create 4096 in
  let s = Bytes.create 2048 in
  while begin
    let l = input ic s 0 (Bytes.length s) in
    if l > 0 then begin
      Buffer.add_bytes buf (Bytes.sub s 0 l);
      true
    end else begin
      false
    end
  end do () done;
  Buffer.contents buf

let file_get_contents f =
  with_open_in f read

(** Sniff the size of the terminal for optimal use of the width. *)
let theight, twidth =
  let height, width = ref 0, ref 0 in
  match
    Scanf.sscanf (List.hd (Process.read_stdout "stty" [|"size"|])) "%d %d" (fun h w ->
      height := h;
      width := w);
    !height, !width
  with
  | exception _ ->
      24, 80
  | 0, 0 ->
      24, 80
  | h, w ->
      h, w


let parse the_parser arg =
  let the_parser = MenhirLib.Convert.Simplified.traditional2revised the_parser in
  let lexbuf = Sedlexing.Utf8.from_string arg in
  try
    the_parser (fun _ -> Lexer.token lexbuf)
  with Sedlexing.MalFormed | Sedlexing.InvalidCodepoint _ | Parser.Error as e ->
    KPrint.bprintf "Syntax error in: %s\n" arg;
    raise e
