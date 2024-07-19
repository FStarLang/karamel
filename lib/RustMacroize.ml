(* Rewritings on the Rust AST after translation and mutability inference *) 

open MiniRust

(* Loop unrolling introduces an implicit binder that does not interact well
   with the substitutions occurring in mutability inference.
   We perform it after the translation *)
let unroll_loops = object
  inherit [_] map_expr as super
  method! visit_For _ b e1 e2 =
    let e2 = super#visit_expr () e2 in 

    match e1 with
    | Range (Some (Constant (UInt32, init as k_init) as e_init), Some (Constant (UInt32, max)), false)
      when (
        let init = int_of_string init in
        let max = int_of_string max in
        let n_loops = max - init in
        n_loops <= !Options.unroll_loops
      ) ->
        let init = int_of_string init in
        let max = int_of_string max in
        let n_loops = max - init in 

        if n_loops = 0 then Unit

        else if n_loops = 1 then subst e_init 0 e2

        else Call (Name ["krml"; "unroll_for!"], [], [
          Constant (CInt, string_of_int n_loops);
          ConstantString b.name;
          Constant k_init;
          Constant (UInt32, "1");
          e2
        ])

    | _ -> For (b, e1, e2)
end 

let macroize files =
  let files =
    List.fold_left (fun files (filename, decls) ->
      let decls = List.fold_left (fun decls decl ->
        match decl with
        | Function ({ body; _ } as f) ->
          let body = unroll_loops#visit_expr () body in
          Function {f with body} :: decls
        | _ -> decl :: decls
      ) [] decls in
      let decls = List.rev decls in
      (filename, decls) :: files
    ) [] files
  in
  List.rev files
