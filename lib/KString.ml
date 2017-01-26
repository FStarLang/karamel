let starts_with s s' =
  String.length s >= String.length s' && String.sub s 0 (String.length s') = s'

let chop s s' =
  assert (starts_with s s');
  let l = String.length s in
  let l' = String.length s' in
  String.sub s l' (l - l')

let split_on_char sep s =
  let open String in
  let r = ref [] in
  let j = ref (length s) in
  for i = length s - 1 downto 0 do
    if unsafe_get s i = sep then begin
      r := sub s (i + 1) (!j - i - 1) :: !r;
      j := i
    end
  done;
  sub s 0 !j :: !r

let exists s s' =
  let r = Str.regexp_string s' in
  try
    ignore (Str.search_forward r s 0);
    true
  with Not_found ->
    false
