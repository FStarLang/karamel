let starts_with s s' =
  String.length s >= String.length s' && String.sub s 0 (String.length s') = s'
