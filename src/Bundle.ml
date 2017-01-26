(** The type of a single bundle -- this avoids a cyclic dependency between
 * [Parser] and [Bundles] *)

(** Crypto.Chacha20=Crypto.Symmetric.Chacha20.*,Crypto.Flag *)
type t = string list * pat list

and pat =
  | Module of string list
  | Prefix of string list
