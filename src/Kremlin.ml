(** KreMLin, a tool to translate from a minimal ML-like language to C. *)

let _ =
  let arg_print = ref false in
  let filename = ref "" in
  let usage = "KreMLin: from a ML-like subset to C\n\
    Usage: " ^ Sys.argv.(0) ^ " [OPTIONS] FILE\n"
  in
  Arg.parse [
    "-print", Arg.Set arg_print, " pretty-print the input AST"
  ] (fun f ->
    filename := f
  ) usage;

  if !filename = "" then begin
    print_endline usage;
    exit 1
  end;

  let files = Ast.read_file !filename in
  let files = Simplify.simplify files in
  if !arg_print then
    let open PPrint in
    Printf.printf "Read [%s]. Printing with w=%d\n" (!filename) Ast.Print.twidth;
    Ast.Print.print (Ast.Print.print_files files ^^ hardline)
