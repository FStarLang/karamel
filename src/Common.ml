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
      (** An F* private qualifier. *)
  | WipeBody
      (** The body must be wiped out -- surfaced in F* via the noextract
       * keyword. *)
  | CInline
      (** User demanded a C inline keyword *)
  | Substitute
      (** User used [@ Substitute ] -- function inlined at call-site, but not
       * necessarily removed. *)
  | GcType
      (** Automatic insertion of pointers because this type will be collected
       * by a conservative garbage collector. *)
  | Comment of string
      (** The function contained a comment. *)
  | MustDisappear
      (** This function *must* disappear, i.e. it shall be inlined at call-site
       * and its definition shall be removed entirely. Used for Ghost and
       * StackInline functions. *)
  [@@deriving yojson,show]
