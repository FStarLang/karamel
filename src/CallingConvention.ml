type t =
  | StdCall
  | CDecl
  | FastCall
  [@@deriving yojson]
