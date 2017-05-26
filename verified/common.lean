import init.function
open function
open tactic

namespace common

@[reducible] def field : Type := string
@[reducible] def block_id : Type := nat
@[reducible] def glob : Type := nat

@[reducible] def ident : Type := nat
@[reducible] def idents := set ident

def fresh_ident : idents → ident := sorry

def location : Type :=
  block_id × nat × list field

inductive value : Type
| int : nat → value
| unit : value
-- | struct : list (field × value) → value
| loc : location → value

-- nested abstract syntax utilities

prefix `^`:70 := option

def option_map {X Y} (f : X → Y) : ^X → ^Y
| none := none
| (some x) := some (f x)

prefix `^^`:70 := option_map

-- "names" mappings, of types [X → ident]
-- used to relate names of free variables in nominal representation, and free
-- variables in nested abstract syntax

def names_empty : empty → ident :=
  empty.rec _

def names_cons {X} (id : ident) (names : X → ident) : ^X → ident
| none := id
| (some y) := names y

def fresh_in {X} (names : X → ident) (id : ident) : Prop :=
  ∀ (x : X), ¬ (id = names x)

lemma names_cons_injective {X} (names : X → ident) (id : ident) :
  injective names →
  fresh_in names id →
  injective (names_cons id names) :=
begin
  intros Hi Hf y1 y2 H,
  cases y1 with y1; cases y2 with y2;
  try {simp [names_cons] at H};
  simp [fresh_in] at Hf;
  try { [smt] add_lemma Hf, ematch },
  -- congruence?
  rw [Hi H]
end

end common
