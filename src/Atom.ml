(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

type t = int
  [@@deriving yojson, show]

let r = ref 0

let fresh () =
  incr r;
  !r

let equal = (=)

let compare = compare
