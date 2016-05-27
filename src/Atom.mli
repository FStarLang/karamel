(** Open variables. *)

type t

val fresh: unit -> t
val equal: t -> t -> bool
