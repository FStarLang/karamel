let file name =
  List.exists (fun p -> Bundle.pattern_matches p name) !Options.drop

let lid lid =
  let f = String.concat "_" (fst lid) in
  file f
