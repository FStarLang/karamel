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

let main (): FStar.HyperStack.ST.ST Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  C.exit_success
