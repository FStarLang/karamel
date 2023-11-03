(* Actually printing out Rust *)

open PPrint

let rust_name f = f ^ ".rs"

let write_file file =
  let prefix, decls = file in
  if decls <> [] then
    (* TODO: directory structure according to the prefix *)
    let filename = KList.last prefix in
    Utils.with_open_out_bin (Output.in_tmp_dir (rust_name filename)) (fun oc ->
      let doc = separate_map (hardline ^^ hardline) (PrintMiniRust.print_decl prefix) decls in
      PPrint.ToChannel.pretty 0.95 100 oc doc
    )

let write_all files =
  Driver.maybe_create_output_dir ();
  List.iter write_file files
