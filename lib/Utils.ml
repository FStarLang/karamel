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
  let c = open_in file_path in
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

let run_and_read cmd =
  let ic = Unix.open_process_in cmd in
  let l = in_channel_length ic in
  really_input_string ic l
