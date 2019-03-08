(* VD: This file will also need to be automatically generated *)

let _ =
  Format.set_formatter_out_channel (open_out_bin "bindings/Lowlevel_stubs.ml");
  Cstubs.write_ml Format.std_formatter ~prefix:"" (module Lowlevel_bindings.Bindings);

  Format.set_formatter_out_channel (open_out_bin "bindings/Lowlevel_c_stubs.c");
  Format.printf "#include \"Lowlevel.h\"\n";
  Cstubs.write_c Format.std_formatter ~prefix:"" (module Lowlevel_bindings.Bindings)
