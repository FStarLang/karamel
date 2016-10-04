(** Some of these will be filled by [Driver]. In particular, the following are
 * automatically added:
 * $krml_home/kremlib/kremlib.c is added to c_files
 * $krml_home/kremlib is added to includes
 *)
let no_prefix: string list ref = ref [ "C" ]
let add_include: string list ref = ref [ "\"kremlib.h\"" ]
let warn_error = ref "+1-2+3..5"
let tmpdir = ref "."
let includes: string list ref = ref []
let verbose = ref false
let exe_name = ref ""
