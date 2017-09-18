type calling_convention =
  | StdCall
  | CDecl
  | FastCall
  [@@deriving yojson,show]

type lifetime =
  | Eternal
  | Stack
  [@@deriving yojson,show]

type flag =
  | Private
  | NoExtract
  | CInline
  | Substitute
  | GcType
  | Comment of string
  [@@deriving yojson,show]
