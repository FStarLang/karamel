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
    try
      let len = Unix.read pipe tmp 0 max in
      Buffer.add_subbytes buf tmp 0 len;
      len > 0
    with _ ->
      false
  end do () done;
  Buffer.contents buf

let run exe args =
  let out_in, out_out = Unix.pipe () in
  let err_in, err_out = Unix.pipe () in
  let args = Array.append [| exe |] args in
  let pid = Unix.create_process exe args Unix.stdin out_out err_out in
  Unix.close out_out;
  Unix.close err_out;
  let output = drain out_in in
  let error = drain err_in in
  Unix.close out_in;
  Unix.close err_in;
  let _pid, status = Unix.waitpid [ ] pid in
  status, output, error

let run_and_read exe args =
  let _, out, _ = run exe args in
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
