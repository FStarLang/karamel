(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

let render doc =
  let buf = Buffer.create 1024 in
  PPrint.ToBuffer.pretty 0.95 Utils.twidth buf doc;
  Buffer.contents buf

let print doc =
  PPrint.ToChannel.pretty 0.95 Utils.twidth stdout doc
