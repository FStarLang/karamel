(** Getting rid of patterns and decompiling pattern matches. *)

open Ast

(* First thing: get rid of tuples, and allocate struct definitions for them. *)
module Gen = struct
  let type_defs = ref []

  let nth_field i =
    match i with
    | 0 -> "fst"
    | 1 -> "snd"
    | 2 -> "thd"
    | _ -> Printf.sprintf "f%d" i

  let ns = [ "Pair" ]

  let tuple (ts: typ list) =
    try
      List.assoc ts !type_defs
    with Not_found ->
      let doc =
        let open PPrint in
        let open PrintAst in
        separate_map underscore print_typ ts
      in
      let lid = ns, KPrint.bsprintf "%a" PrintCommon.pdoc doc in
      let fields = List.mapi (fun i t ->
        nth_field i, (t, false)
      ) ts in
      let type_def = DType (lid, Flat fields) in
      type_defs := (ts, (lid, type_def)) :: !type_defs;
      lid, type_def

  let get () =
    List.rev_map (fun (_, (_, d)) -> d) !type_defs
end


let record_of_tuple = object(self)

  inherit [unit] map

  method! etuple () _ es =
    EFlat (List.mapi (fun i e ->
      Gen.nth_field i, self#visit () e
    ) es)

  method! ttuple () ts =
    let lid, _ = Gen.tuple (List.map (self#visit_t ()) ts) in
    TQualified lid

  method! ptuple () _ pats =
    PRecord (List.mapi (fun i p -> Gen.nth_field i, self#visit_pattern () p) pats)

end

let drop_tuples files =
  let files = Simplify.visit_files () record_of_tuple files in
  ("Pair", Gen.get ()) :: files
