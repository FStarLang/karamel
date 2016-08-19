(** Open variables. *)

type t
  [@@deriving yojson]

val fresh: unit -> t
val equal: t -> t -> bool
