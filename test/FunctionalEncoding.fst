module FunctionalEncoding

type animal_species = | Giraffe | Elephant

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
