module ExitCode

open FStar.HyperStack.ST

let main (): Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true) =
  C.EXIT_SUCCESS
