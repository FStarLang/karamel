module SystemNative

(* This module is not extracted by KreMLin; rather, whichever functions are
 * exposed here are implemented in C. Since this module does not get a prefix,
 * it may be the case that an enum case (e.g. AI_PASSIVE) is extracted as
 * AI_PASSIVE which happens to *exactly* match the macro. In other cases, stubs
 * might be needed. *)

module S = FStar.Seq
module B = FStar.Buffer
module U8 = FStar.UInt8
module I32 = FStar.UInt8
module U32 = FStar.UInt32

(* Strings *******************************************************************)

(* The C char type is abstract, as it should be: it's just a byte of data.
 * However, one can happily convert a `char` as a standard unsigned 8-bit
 * integer. *)
val uint8_of_char: C.char -> U8.t

(* Buffers don't have equality but we can certainly test whether they're null. *)
val is_null: (#a: Type) -> Buffer.buffer a -> bool

(* Universal null pointer. *)
val null: (a: Type) -> Pure (Buffer.buffer a) (requires True) (ensures (fun b -> is_null b))

(* String in the C sense: we're modeling low-level systems-y things. They're
 * zero-terminated. *)
type mstring_t =
  b:Buffer.buffer C.char {
    if is_null b then
      True
    else
      forall h.
      B.length b > 0 /\
      uint8_of_char (S.index (Buffer.as_seq h b) (Buffer.length b - 1)) = 0uy
  }

(* C.string is "const char *" and the only way to create it is to use
 * C.string_of_literal, where extraction checks that a literal is indeed passed
 * to it. So, expose the right value. *)
val null_string: C.string

(* Useful shorthand. *)
type pointer (t: Type0) =
  b:B.buffer t { B.length b = 1 }

type pointer_or_null (t: Type0) =
  b:B.buffer t { if is_null b then True else B.length b = 1 }

(* Standard ******************************************************************)

(* Relying on the fact that C11 enums are inter-convertible with int. *)
type exit_code_t = | EXIT_SUCCESS | EXIT_FAILURE


(* Network *******************************************************************)

type ai_family_t = | PF_INET | PF_INET6
type ai_flag_t = | AI_PASSIVE | AI_CANONNAME | AI_NUMERICHOST
type ai_socktype_t = | SOCK_STREAM | SOCK_DGRAM
type ai_protocol_t = | IPPROTO_TCP | IPPROTO_UDP
type socklen_t = U32.t

(* By hand: *)
val or_flags: ai_flag_t -> ai_flag_t -> ai_flag_t
val ai_protocol_any: ai_protocol_t

assume type sockaddr_in_t
assume type sockaddr_in6_t
let sockaddr_t (af: ai_family_t) =
  match af with
  | PF_INET -> pointer_or_null sockaddr_in_t
  | PF_INET6 -> pointer_or_null sockaddr_in6_t

(*
  struct addrinfo {
          int	ai_flags;	/* AI_PASSIVE, AI_CANONNAME, AI_NUMERICHOST */
          int	ai_family;	/* PF_xxx */
          int	ai_socktype;	/* SOCK_xxx */
          int	ai_protocol;	/* 0 or IPPROTO_xxx for IPv4 and IPv6 */
          socklen_t ai_addrlen;	/* length of ai_addr */
          char	*ai_canonname;	/* canonical name for hostname */
          struct	sockaddr *ai_addr;	/* binary address */
          struct	addrinfo *ai_next;	/* next structure in linked list */
  };
*)
noeq type addrinfo_t =
  | AddrInfo:
    ai_flags: ai_flag_t ->
    ai_family: ai_family_t ->
    ai_socktype: ai_socktype_t ->
    ai_protocol: ai_protocol_t ->
    ai_addrlen: socklen_t ->
    ai_canonname: mstring_t ->
    ai_addr: sockaddr_t ai_family ->
    ai_next: pointer_or_null addrinfo_t ->
    addrinfo_t

val addrinfo_length (p: pointer_or_null addrinfo_t): GTot nat
val addrinfo_length_decreases: (h: HyperStack.mem) -> (p: pointer_or_null addrinfo_t) ->
  Lemma
    (ensures (
      if is_null p then
        addrinfo_length p = 0
      else
        addrinfo_length p = addrinfo_length (Buffer.get h p 0).ai_next + 1))
  [ SMTPat (addrinfo_length p); SMTPat (Buffer.get h p 0) ]

let rec addrinfo_live h (p: pointer_or_null addrinfo_t): GTot Type0 (decreases (addrinfo_length p)) =
  let l = addrinfo_length p in
  if l = 0 then
    b2t (is_null p)
  else
    Buffer.live h p /\
    addrinfo_live h (Buffer.get h p 0).ai_next

open FStar.HyperStack.ST

(* Note: do we need to enforce res[0] != hints? Would the syscall work? *)
val getaddrinfo:
  node:C.string ->
  service:C.string ->
  hints: pointer addrinfo_t ->
  res: pointer (pointer_or_null addrinfo_t) ->
  Stack Int32.t
    (requires (fun h0 ->
      Buffer.live h0 hints /\
      Buffer.live h0 res))
    (ensures (fun h0 status h1 ->
      Buffer.live h1 hints /\
      Buffer.live h1 res /\
      modifies_none h0 h1 /\
      (status = 0l ==>
        addrinfo_live h1 (Buffer.get h1 res 0))))

// say that a buffer not reachable through `ai` remains live
val freeaddrinfo: ai:pointer_or_null addrinfo_t ->
  Stack unit
    (requires (fun h0 ->
      addrinfo_live h0 ai))
    (ensures (fun h0 () h1 -> True))
