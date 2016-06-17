let render doc =
  let buf = Buffer.create 1024 in
  PPrint.ToBuffer.pretty 0.95 twidth buf doc;
  Buffer.contents buf

let print doc =
  PPrint.ToChannel.pretty 0.95 twidth stdout doc
