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
  let buf = Buffer.create 2048 in
  let tmp = Bytes.create max in
  while begin
    let len = Unix.read pipe tmp 0 max in
    Buffer.add_subbytes buf tmp 0 len;
    len = max
  end do () done;
  Buffer.contents buf

let run exe args =
  let pipe_in, pipe_out = Unix.pipe () in
  let args = Array.append [| exe |] args in
  let pid = Unix.create_process exe args Unix.stdin pipe_out Unix.stderr in
  let output = drain pipe_in in
  Unix.close pipe_in;
  Unix.close pipe_out;
  let _pid, status = Unix.waitpid [ Unix.WNOHANG ] pid in
  status, output

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
