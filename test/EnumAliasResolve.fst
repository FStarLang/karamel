module EnumAliasResolve

(* Establish dependency so both .krml files are extracted and bundled. *)
let _dep: EnumAliasHelper.status = EnumAliasHelper.Active

(* This type has the same constructor names (Active, Inactive) as
   EnumAliasHelper.status. The DataTypes pass will share the tag enum,
   making one type an abbreviation of the other. Without resolve_abbrev
   in AstToCStar, mangle_enum produces the wrong name for the alias type. *)
type mode = | Active | Inactive

let check_mode (m: mode): FStar.Int32.t =
  match m with
  | Active -> 1l
  | Inactive -> 0l

let main () =
  if check_mode Active = 1l then 0l else 1l
