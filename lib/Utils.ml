let try_finally f h =
  let result =
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

let with_open_out file_path f =
  let c = open_out file_path in
  try_finally (fun () ->
    f c
  ) (fun () ->
    close_out c
  )

let drain pipe =
  let max = 2048 in
  let bufs = ref [] in
  let buf = Bytes.create max in
  while begin
    let len = Unix.read pipe buf 0 2048 in
    bufs := Bytes.to_string (Bytes.sub buf 0 len) :: !bufs;
    len = max
  end do () done;
  String.concat "" (List.rev !bufs)

let run exe args =
  let pipe_out, pipe_in = Unix.pipe () in
  let args = Array.append [| exe |] args in
  let pid = Unix.create_process exe args Unix.stdin pipe_in Unix.stderr in
  let out = drain pipe_out in
  let _pid, status = Unix.waitpid [] pid in
  status, out

let run_and_read exe args =
  let _, out = run exe args in
  out

(** Sniff the size of the terminal for optimal use of the width. *)
let theight, twidth =
  let height, width = ref 0, ref 0 in
  match
    Scanf.sscanf (run_and_read "stty" [|"size"|]) "%d %d" (fun h w ->
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
