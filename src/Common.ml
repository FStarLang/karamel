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

type source_info = {
  file_name : string;
  mod_name : string list;
  position : (int * int) (* line + col, note: col is always 0 for the time being *)
} [@@deriving yojson,show]

let dummy_src_info = {
  file_name = "INTERNAL";
  mod_name  = [];
  position = (0, 0);
}
