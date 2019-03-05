(* VD: This file will also need to be automatically generated *)

let _ =
  let path_ml = "bindings/Lowlevel_stubs.ml" in
  Format.set_formatter_out_channel (open_out_bin path_ml);
  Cstubs.write_ml Format.std_formatter ~prefix:"" (module Lowlevel_bindings.Bindings);

  let path_c = "bindings/Lowlevel_c_stubs.c" in
  Format.set_formatter_out_channel (open_out_bin path_c);
  Format.printf "#include \"Lowlevel.h\"\n";
  Cstubs.write_c Format.std_formatter ~prefix:"" (module Lowlevel_bindings.Bindings)
