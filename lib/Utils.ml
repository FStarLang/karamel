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

let run_and_read exe args =
  let pipe_out, pipe_in = Unix.pipe () in
  let args = Array.append [| exe |] args in
  let _pid = Unix.create_process exe args Unix.stdin pipe_in Unix.stderr in
  let bufs = ref [] in
  let max = 2048 in
  let buf = Bytes.create max in
  while begin
    let len = Unix.read pipe_out buf 0 2048 in
    bufs := Bytes.to_string (Bytes.sub buf 0 len) :: !bufs;
    len = max
  end do () done;
  String.concat "" (List.rev !bufs)
