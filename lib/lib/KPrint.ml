let bsprintf fmt =
  Printf.kbprintf Buffer.contents (Buffer.create 16) fmt

let bfprintf oc fmt =
  Printf.kbprintf (Buffer.output_buffer oc) (Buffer.create 16) fmt

let bprintf fmt =
  bfprintf stdout fmt

let beprintf fmt =
  bfprintf stderr fmt

let p = PPrint.ToBuffer.compact
