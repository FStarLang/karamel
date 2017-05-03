let should_drop name =
  List.exists (fun p -> Bundle.pattern_matches p name) !Options.drop
