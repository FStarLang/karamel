module FunctionalEncoding

type animal_species = | Giraffe | Elephant

#set-options "--__no_positivity"
noeq type animal = {
  species: animal_species;
  to_string: animal -> string
}

let to_string (animal: animal): string =
  match animal.species with
  | Giraffe -> "Giraffe"
  | Elephant -> "Elephant"

let new_giraffe () = {
  species = Giraffe;
  to_string = to_string
}

open FStar.HyperStack.ST

let main () =
  C.EXIT_SUCCESS
