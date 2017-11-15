module HelloSystem

open FStar.HyperStack.ST
open FStar.HyperStack
open SystemNative
open FStar.Buffer

let main (): Stack FStar.Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  push_frame ();
  let hints: addrinfo_t = AddrInfo
    AI_PASSIVE
    PF_INET
    SOCK_STREAM
    ai_protocol_any
    0ul
    (null C.char)
    (null sockaddr_in_t)
    (null addrinfo_t)
  in
  let hints = Buffer.create hints 1ul in
  let servinfo = Buffer.create (null addrinfo_t) 1ul in
  let status = getaddrinfo null_string (C.String.of_literal "3490") hints servinfo in
  if status = 0l then
    freeaddrinfo servinfo.(0ul);
  pop_frame ();
  C.exit_success
