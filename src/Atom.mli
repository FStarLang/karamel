(** Open variables. *)

type t
  [@@deriving yojson,show]

val fresh: unit -> t
val equal: t -> t -> bool
val compare: t -> t -> int
