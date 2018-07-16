type calling_convention =
  | StdCall
  | CDecl
  | FastCall
  [@@deriving yojson,show]

type lifetime =
  | Eternal
  | Stack
  | Heap
  [@@deriving yojson,show]

type flag =
  | Private
      (** An F* private qualifier. *)
  | WipeBody
      (** Should now be unused. Left there for compatibility with previous ASTs. *)
  | Inline
      (** User demanded a C inline keyword *)
  | Substitute
      (** User used [@ Substitute ] -- function inlined at call-site, but not
       * necessarily removed. Deprecated in favor of using inline_for_extraction
       * at the F* level. *)
  | GcType
      (** Automatic insertion of pointers because this type will be collected
       * by a conservative garbage collector. *)
  | Comment of string
      (** The function contained a comment. *)
  | MustDisappear
      (** This function *must* disappear, i.e. it shall be inlined at call-site
       * and its definition shall be removed entirely. Used for Ghost and
       * StackInline functions. *)
  | Const of string
      (** Identify a parameter by name, to be marked as const. *)
  | Prologue of string
      (** Verbatim C code, inserted before. *)
  | Epilogue of string
      (** Verbatim C code, inserted after. *)
  | Abstract
      (** C abstract struct with only a forward declaration in the header. *)
  [@@deriving yojson,show]
