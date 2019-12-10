module Comment
open FStar.HyperStack.ST

module LC = LowStar.Comment

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  LC.comment "this comment should NOT be erased";
  LC.comment_gen "comment before" C.EXIT_SUCCESS "comment after"
