(** Open variables. *)

type t
  [@@deriving yojson,show]

val fresh: unit -> t
val equal: t -> t -> bool
