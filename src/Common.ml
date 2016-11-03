type calling_convention =
  | StdCall
  | CDecl
  | FastCall
  [@@deriving yojson]

type lifetime =
  | Stack
  | Eternal
  [@@deriving yojson]

type flag =
  | Private
  [@@deriving yojson]

