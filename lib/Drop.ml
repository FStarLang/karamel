(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

let file name =
  List.exists (fun p -> Bundle.pattern_matches p name) !Options.drop

let lid lid =
  let f = String.concat "_" (fst lid) in
  file f || List.exists (fun p -> p = Bundle.Lid lid) !Options.drop
