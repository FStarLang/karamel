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

lemma fresh_ident_spec : ∀ ids, ¬(fresh_ident ids ∈ ids) :=
  sorry

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

def names_in {X} (names : X → ident) (ids : set ident) : Prop :=
  ∀ (x : X), names x ∈ ids

lemma fresh_ident_fresh {X} (names : X → ident) (seen : set ident) :
  names_in names seen →
  fresh_in names (fresh_ident seen)
:=
begin
  intros H x H',
  note hh := H x,
  apply fresh_ident_spec, rewrite H', apply hh
end

lemma names_in_cons {X} (names : X → ident) (ids : set ident) :
  names_in names ids →
  names_in (names_cons (fresh_ident ids) names) (set.insert (fresh_ident ids) ids)
:=
begin
  intros H x,
  cases x with x; simp [names_cons],
  { admit }, -- FIXME TODO
  { note HH := H x, admit } -- FIXME TODO
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


-- Generic mechanism for naming new elements added to the context by some tactic
--
-- This is useful for tactics that may add many new terms to the context, in a
-- way that is hard to track by the tactic itself. For example, some new terms
-- may be introduced, but disappear later on after rewriting some equality using
-- `subst`.
--
-- We would still like to be able to name the new expressions that appear in the
-- final context, using user-provided names.
--
-- The [with_names] helper provides a generic way to do that: it takes a [tac]
-- tactic, and a list [ns] of user-provided names. It runs [tac] with a
-- reference [r]. [tac] may then allocate new names using [fresh_name r]. Then,
-- [with_names] will rename the fresh names that actually appear in the final
-- context using the user provided names [ns].
--
-- The optional [reverse] argument indicates whether the user-provided names
-- should be used to name the fresh names in the order they have been generated,
-- or in reverse order. By default (reverse = false), they are named in the
-- same order as generated.

meta def get_name : list name → tactic (name × list name)
| (n :: ns) := return (n, ns)
| [] := failed

meta def rnm h ns := do
  (do (n, ns) ← get_name ns, rename h n, return ns) <|>
  return ns

meta def fresh_name (used : ref (list name)) (suggestion : name) : tactic name :=
do
  n ← get_unused_name suggestion none,
  ns ← read_ref used,
  write_ref used (n :: ns),
  return n

meta def with_names {α : Type}
  (tac : ref (list name) → tactic α)
  (ns : list name)
  (reverse : bool := false) :
  tactic α
:=
  using_new_ref [] $ λ r, do
    ret ← tac r,
    temp_ns ← read_ref r,
    ctx ← local_context,
    list.mfoldl (λ ns temp_n,
      (get_local temp_n >> rnm temp_n ns) <|> return ns
    ) ns (if reverse then temp_ns else list.reverse temp_ns),
    return ret

private meta def test (r : ref (list name)) : tactic unit :=
do
  a ← fresh_name r `a,
  pose a none mk_true,
  b ← fresh_name r `b,
  pose b none mk_false,
  return ()

example : 0 = 0 :=
begin
  with_names test [`foo, `bar], refl
end

-- An inversion tactic for hypothesis of the form [a >>= (λx, b) = some res].
--
-- Produces new hypothesis of the form [a = some _], [b x = some _], ...
-- (also tries to [subst] the produced equalities when possible)
--
-- Inspired by monadInv from CompCert (in Errors.v)

meta def opt_inv_core (r : ref (list name)) : name → tactic unit := λ h,
do
  ty ← get_local h >>= infer_type,
  match ty with
  | `(some _ = some _) :=
  do
    injection1_clean h,
    (get_local h >>= subst) <|>
    (do a ← fresh_name r `a, b ← fresh_name r `b,
        get_local h >>= λ H, injection_with H [a, b],
        get_local a >>= subst,
        get_local b >>= subst,
        get_local h >>= clear)

  | `(bind _ _ = some _) :=
  do
    e ← get_local h >>= λH, i_to_expr ``(option_bind_inv _ _ _ %%H),
    get_local h >>= clear,
    he ← fresh_name r `he, h' ← fresh_name r `h',
    eq1 ← fresh_name r `eq1, eq2 ← fresh_name r `eq2,
    x ← fresh_name r `x,

    note he none e,
    get_local he >>= λ H, cases H [x, h'],
    xτ ← get_local x >>= infer_type,
    (match xτ with
     | `(_ × _) := do
       x1 ← fresh_name r `x1, x2 ← fresh_name r `x2,
       get_local x >>= λ x, cases x [x1, x2]
     | _ := skip
     end),
    get_local h' >>= λ H, cases H [eq1, eq2],

    get_local eq2 >>= λ E, try (dsimp_at E),
    try (opt_inv_core eq1),
    try (opt_inv_core eq2)
  | _ := fail "meh"
  end

meta def opt_inv (h : name) (ns : list name) : tactic unit :=
  with_names (λ r, opt_inv_core r h) ns true

end tactic

namespace tactic.interactive
open lean lean.parser
open interactive interactive.types tactic

meta def opt_inv (h : parse ident) (ns : parse with_ident_list) : tactic unit :=
  tactic.opt_inv h ns >> skip

-- meta def injections_subst (h : parse ident) : tactic unit :=
-- do tactic.get_local h >>= tactic.injections_subst,
--    tactic.get_local h >>= tactic.clear

meta def trans (e : parse texpr) : tactic unit :=
  apply ``(@eq.trans _ _ %%e _)

end tactic.interactive
