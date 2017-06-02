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

section
universes u

inductive pempty : Type u

end

prefix `^`:70 := option

def option_map {X Y} (f : X → Y) : ^X → ^Y
| none := none
| (some x) := some (f x)

prefix `^^`:70 := option_map

-- "names" mappings, of types [X → ident]
-- used to relate names of free variables in nominal representation, and free
-- variables in nested abstract syntax

def names_empty : pempty → ident :=
  pempty.rec _

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
  simp [names_cons] at H;
  simp [fresh_in] at Hf,
  { [smt] add_lemma Hf, ematch },
  { [smt] add_lemma Hf, ematch },
  -- congruence?
  rw [Hi H]
end

end common

-- tactics

lemma option_bind_inv {X Y : Type} (o : option X) (f : X → option Y) : ∀ y,
  o >>= f = some y →
  ∃ x, o = some x ∧ f x = some y
:=
begin
  intros _ H,
  cases o with x; dsimp [`has_bind.bind, option_bind] at H,
  { injection H },
  { existsi x, split, refl, assumption }
end

-- namespace names_tactic
-- meta def names_state := list name
-- meta def names_tactic := state_t names_state tactic

-- meta instance : monad names_tactic := state_t.monad _ _

-- meta instance : monad.has_monad_lift tactic names_tactic :=
--   monad.monad_transformer_lift (state_t _) tactic

-- meta instance (α : Type) : has_coe (tactic α) (names_tactic α) :=
--   ⟨monad.monad_lift⟩

-- meta def fresh_name (suggestion : name) : names_tactic name := λ ns,
--   do n ← get_unused_name suggestion none,
--      return (n, n::ns)
-- end names_tactic

namespace tactic

open tactic expr
open lean lean.parser

meta def injection1_clean (h : name) :=
do
  h' ← mk_fresh_name,
  (get_local h >>= λ H, injection_with H [h']),
  (get_local h >>= clear),
  rename h' h


-- meta def injections : expr → tactic (list expr) := λ e,
-- do
--   es ← (injection e >>= mmap injections) <|> return [[e]],
--   return (list.join es)

-- meta def injections_subst (e : expr) : tactic unit :=
-- do
--   es ← injections e,
--   mfor' es subst


-- FIXME: naming of things is not perfect: the existentially quantified variable
-- is systematically named using one of the provided names (`x`), however it may
-- disappear completely from the context after doing the substs of the base case
--
-- One solution would be maybe to name everything using temporary fresh names,
-- and keep track of these names; and at the end, check which of these names
-- still appear in the context, and rename those using the provided names. Maybe there's an existing auxiliary function which does that?

meta def get_name : list name → tactic (name × list name)
| (n :: ns) := return (n, ns)
| ns := do n ← get_unused_name `H none, return (n, ns)

meta def rnm h ns := do
  (n, ns) ← get_name ns,
  rename h n,
  return ns

meta def opt_inv : name → list name → tactic (list name) := λ h ns,
do
  ty ← get_local h >>= infer_type,
  match ty with
  | `(some _ = some _) :=
  do
    injection1_clean h,
    (get_local h >>= subst >> return ns) <|>
    (do a ← get_unused_name `a none, b ← get_unused_name `b none,
        get_local h >>= λ H, injection_with H [a, b],
        get_local a >>= subst,
        get_local b >>= subst,
        get_local h >>= clear,
        return ns) <|>
    rnm h ns

  | `(bind _ _ = some _) :=
  do
    e ← get_local h >>= λH, i_to_expr ``(option_bind_inv _ _ _ %%H),
    get_local h >>= clear,
    he ← get_unused_name `he none, h' ← get_unused_name `h' none,
    eq1 ← get_unused_name `eq1 none, eq2 ← get_unused_name `eq2 none,
    (x, ns) ← get_name ns,

    note he none e,
    get_local he >>= λ H, cases H [x, h'],
    get_local h' >>= λ H, cases H [eq1, eq2],

    get_local eq2 >>= λ E, try (dsimp_at E),
    ns ← (opt_inv eq1 ns <|> rnm eq1 ns),
    ns ← (opt_inv eq2 ns <|> rnm eq2 ns),
    return ns
  | _ := fail "meh"
  end

end tactic

namespace tactic.interactive
open lean lean.parser
open interactive interactive.types tactic

meta def opt_inv (h : parse ident) (ns : parse with_ident_list) : tactic unit :=
  tactic.opt_inv h ns >> skip

-- meta def injections_subst (h : parse ident) : tactic unit :=
-- do tactic.get_local h >>= tactic.injections_subst,
--    tactic.get_local h >>= tactic.clear

end tactic.interactive
