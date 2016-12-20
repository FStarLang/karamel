type calling_convention =
  | StdCall
  | CDecl
  | FastCall
  [@@deriving yojson]

type lifetime =
  | Eternal
  | Stack
  [@@deriving yojson]

type flag =
  | Private
  | NoExtract
  | CInline
  | Substitute
  [@@deriving yojson]

