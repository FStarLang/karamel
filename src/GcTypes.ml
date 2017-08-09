(* Transformations specifically in support of types marked as GcType. We
 * essentially:
 * - replace every occurrence of [t] with [t*]
 * - replace every pattern match on a [t] with a pattern on [*t]
 * - replace every literal (cons) [e] of type [t] with [bufcreate 1 e]
 * - replace every [e.f] where [e] is of type [t] with [bufread e 0.f]
 *)

open Ast
open Helpers

let mk_table files =
  Helpers.build_map files (fun map -> function
    | DType (lid, flags, _, _) when List.mem Common.GcType flags ->
        Hashtbl.add map lid ()
    | _ ->
        ()
  )

let is_gc table = function
  | TQualified lid when Hashtbl.mem table lid ->
      true
  | _ ->
      false

let alloc table = object (_self)

  inherit [unit] map

  method! tqualified _env lid =
    if Hashtbl.mem table lid then
      TBuf (TQualified lid)
    else
      TQualified lid

end

let heap_allocate_gc_types files =
  let table = mk_table files in
  let files = if false then visit_files () (alloc table) files else files in
  files
