let rec filter_mapi i f l =
  match l with
  | [] ->
      []
  | x :: l ->
      match f i x with
      | Some x ->
          x :: filter_mapi (i + 1) f l
      | None ->
          filter_mapi (i + 1) f l

let filter_mapi f l =
  filter_mapi 0 f l

let filter_some l = List.filter_map Fun.id l

let rec filter_mask mask l =
  match mask, l with
  | true :: mask, x :: l ->
      x :: filter_mask mask l
  | false :: mask, _ :: l ->
      filter_mask mask l
  | [], [] ->
      []
  | _ ->
      invalid_arg "filter_mask"

let fold_lefti f s l =
  snd @@ List.fold_left (fun (i, s) x -> (i + 1, f i s x)) (0, s) l

(* NOTE: OCaml 5.1 introduces {!Stdlib.List.find_index} which is [index] except
   that it returns an option. *)
let index p l =
  let rec index i l =
    match l with
    | [] ->
        raise Not_found
    | hd :: tl ->
        if p hd then
          i
        else
          index (i + 1) tl
  in
  index 0 l

let split i l =
  let rec split acc i l =
    if i = 0 then
      List.rev acc, l
    else match l with
      | hd :: l ->
          split (hd :: acc) (i - 1) l
      | [] ->
          raise (Invalid_argument "split")
  in
  split [] i l

let split_at_last l =
  let all_but_last, last = split (List.length l - 1) l in
  all_but_last, List.hd last

let rec last = function
  | [] -> failwith "KList.last"
  | [x] -> x
  | _ :: l -> last l

let reduce f l =
  List.fold_left f (List.hd l) (List.tl l)

let one l =
  match l with
  | [ x ] -> x
  | _ -> invalid_arg ("one: argument is of length " ^ string_of_int (List.length l))

(* NOTE: provided by {!Stdlib.List} in OCaml 5.1. *)
let is_empty = function
  | [] -> true
  | _ -> false
