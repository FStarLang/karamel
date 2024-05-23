(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

let file name =
  List.exists (fun p -> Bundle.pattern_matches_file p name) !Options.drop

let lid name =
  List.exists (fun p -> Bundle.pattern_matches_lid p name) !Options.drop
