(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

(* Just some handy shortcuts in a separate module to avoid complexity in the
 * dependency graph. *)

let bundle = Utils.parse Parser.bundle
let drop = Utils.parse Parser.drop
let lid = Utils.parse Parser.lid
