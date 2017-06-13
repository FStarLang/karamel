import common

namespace lowstar

open common

inductive typ : Type
| int : typ
| unit : typ
| buf : typ → typ
| arrow : typ → typ → typ
-- struct?

universe variable u

-- binders are "let_*" cases
inductive exp : Type u → Type (u+1)
| int : ∀ {X}, nat → exp X
| unit : ∀ {X}, exp X
| loc : ∀ {X}, location → exp X
| var : ∀ {X}, X → exp X
-- | struct : list (common.field × exp) → exp
-- | field : ∀ {X}, exp X → common.field → exp X
-- | mut_field : ∀ {X}, exp X → common.field → exp X
| subbuf : ∀ {X}, exp X → exp X → exp X
| if_then_else : ∀ {X}, exp X → exp X → exp X → exp X
| let_in : ∀ {X}, typ → exp X → exp (^X) → exp X
| ignore : ∀ {X}, exp X → exp X → exp X
| let_app : ∀ {X}, typ → glob → exp X → exp (^X) → exp X -- let [x] : τ = f e in e
| let_newbuf : ∀ {X}, nat → exp X → typ → exp (^X) → exp X -- let [x] = newbuf n (e : τ) in e
| let_readbuf : ∀ {X}, typ → exp X → exp X → exp (^X) → exp X -- let [x] : τ = readbuf e e in e
| writebuf : ∀ {X}, exp X → exp X → exp X → exp X → exp X -- let _ = writebuf e e e in e
-- | let_newstruct : ∀ {X}, exp X → typ → exp (^X) → exp X -- let [x] = newstruct (e : τ) in e
--  | let_readstruct : ∀ {X}, typ → exp X → exp (^X) → exp X -- let [x] : τ = readstruct e in e
-- | writestruct : ∀ {X}, exp X → exp X → exp X -- let _ = writestruct e in e
| withframe : ∀ {X}, exp X → exp X
| pop : ∀ {X}, exp X → exp X

-- inductive is_value : ∀ {X : Type u}, exp X → Type (u+1)
-- | is_value_int : ∀ {X} n, is_value (@exp.int X n)
-- | is_value_unit : ∀ {X}, is_value (@exp.unit X)
-- | is_value_loc : ∀ {X} l, is_value (@exp.loc X l)

-- def value : Type (u+1) :=
--   Π {X : Type u}, Σ (e : exp X), is_value e

def exp_of_value : ∀ {X}, value → exp X
| X (value.int n) := @exp.int X n
| X value.unit := @exp.unit X
| X (value.loc l) := @exp.loc X l

instance : ∀ X, has_coe value (exp X) := λX, ⟨exp_of_value⟩

inductive decl : Type (u+1)
| function : glob → typ → exp (^pempty.{u}) → typ → decl
-- | global : glob → typ → value → decl

@[reducible] def program : Type (u+1) := list decl

def find_fundecl (fn : glob) : program → option decl
| [] := none
| (d :: ds) :=
  match d with
  | (decl.function fn' _ _ _) :=
    if fn = fn' then some d else find_fundecl ds
  -- | _ := find_fundecl ds
  end

-- renaming

def exp_map : ∀ {X Y : Type u} (f : X → Y), exp X → exp Y
| X Y f (exp.int n) := exp.int n
| X Y f exp.unit := exp.unit
| X Y f (exp.loc l) := exp.loc l
| X Y f (exp.var x) := exp.var (f x)
-- | struct : list (common.field × exp) → exp
-- | X Y f (exp.field e fd) := exp.field (exp_map f e) fd
-- | X Y f (exp.mut_field e fd) := exp.mut_field (exp_map f e) fd
| X Y f (exp.subbuf e1 e2) := exp.subbuf (exp_map f e1) (exp_map f e2)
| X Y f (exp.if_then_else e1 e2 e3) := exp.if_then_else (exp_map f e1) (exp_map f e2) (exp_map f e3)
| X Y f (exp.let_in τ e1 e2) := exp.let_in τ (exp_map f e1) (exp_map (^^f) e2)
| X Y f (exp.ignore e1 e2) := exp.ignore (exp_map f e1) (exp_map f e2)
| X Y f (exp.let_app τ fn e1 e2) := exp.let_app τ fn (exp_map f e1) (exp_map (^^f) e2)
| X Y f (exp.let_newbuf n e1 τ e2) := exp.let_newbuf n (exp_map f e1) τ (exp_map (^^f) e2)
| X Y f (exp.let_readbuf τ e1 e2 e3) := exp.let_readbuf τ (exp_map f e1) (exp_map f e2) (exp_map (^^f) e3)
| X Y f (exp.writebuf e1 e2 e3 e4) := exp.writebuf (exp_map f e1) (exp_map f e2) (exp_map f e3) (exp_map f e4)
-- | X Y f (exp.let_newstruct e1 τ e2) := exp.let_newstruct (exp_map f e1) τ (exp_map (^^f) e2)
-- | X Y f (exp.let_readstruct τ e1 e2) := exp.let_readstruct τ (exp_map f e1) (exp_map (^^f) e2)
-- | X Y f (exp.writestruct e1 e2) := exp.writestruct (exp_map f e1) (exp_map f e2)
| X Y f (exp.withframe e) := exp.withframe (exp_map f e)
| X Y f (exp.pop e) := exp.pop (exp_map f e)

-- def exp_dist {X : Type u} : ^(exp X) → exp (^X)
-- | none := exp.var none
-- | (some e) := exp_map some e

def f_lift {X Y : Type u} : (X → exp Y) → ^X → exp (^Y)
| f none := exp.var none
| f (some e) := exp_map some (f e)

def exp_bind : ∀ {X Y : Type u}, exp X → (X → exp Y) → exp Y
| X Y (exp.int n) f := exp.int n
| X Y exp.unit f := exp.unit
| X Y (exp.loc l) f := exp.loc l
| X Y (exp.var x) f := f x
-- | X Y (exp.field e fd) f := exp.field (exp_bind e f) fd
-- | X Y (exp.mut_field e fd) f := exp.mut_field (exp_bind e f) fd
| X Y (exp.subbuf e1 e2) f := exp.subbuf (exp_bind e1 f) (exp_bind e2 f)
| X Y (exp.if_then_else e1 e2 e3) f := exp.if_then_else (exp_bind e1 f) (exp_bind e2 f) (exp_bind e3 f)
| X Y (exp.let_in τ e1 e2) f := exp.let_in τ (exp_bind e1 f) (exp_bind e2 (f_lift f))
| X Y (exp.ignore e1 e2) f := exp.ignore (exp_bind e1 f) (exp_bind e2 f)
| X Y (exp.let_app τ fn e1 e2) f := exp.let_app τ fn (exp_bind e1 f) (exp_bind e2 (f_lift f))
| X Y (exp.let_newbuf n e1 τ e2) f := exp.let_newbuf n (exp_bind e1 f) τ (exp_bind e2 (f_lift f))
| X Y (exp.let_readbuf τ e1 e2 e3) f := exp.let_readbuf τ (exp_bind e1 f) (exp_bind e2 f) (exp_bind e3 (f_lift f))
| X Y (exp.writebuf e1 e2 e3 e4) f := exp.writebuf (exp_bind e1 f) (exp_bind e2 f) (exp_bind e3 f) (exp_bind e4 f)
-- | X Y (exp.let_newstruct e1 τ e2) f := exp.let_newstruct (exp_bind e1 f) τ (exp_bind e2 (f_lift f))
-- | X Y (exp.let_readstruct τ e1 e2) f := exp.let_readstruct τ (exp_bind e1 f) (exp_bind e2 (f_lift f))
-- | X Y (exp.writestruct e1 e2) f := exp.writestruct (exp_bind e1 f) (exp_bind e2 f)
| X Y (exp.withframe e) f := exp.withframe (exp_bind e f)
| X Y (exp.pop e) f := exp.pop (exp_bind e f)

def exp_head_subst {X} (t : exp (^X)) (u : exp X) : exp X :=
  exp_bind t (λ x, match x with none := u | some u := exp.var u end)

reserve infix ` ◄ `:75
infix ◄ := exp_head_subst

-- Used to lift the body of a decl.function from a [exp ^pempty] to a [exp ^X]
-- for some given X
def lift_fbody (X : Type u) (e : exp (^pempty.{u})) : exp (^X) :=
  exp_map (option_map ((pempty.rec _) : pempty → X)) e

-- Auxiliary definitions dealing with the names and binders in locally nameless
-- representation

-- def subst (x : var) (u : exp) : exp → exp
-- | (exp.bvar i) := exp.bvar i
-- | (exp.fvar y) := if x = y then u else exp.fvar y
-- -- | (exp.struct s) := sorry
-- | (exp.field e fd) := exp.field (subst e) fd
-- | (exp.mut_field e fd) := exp.mut_field (subst e) fd
-- | (exp.subbuf e1 e2) := exp.subbuf (subst e1) (subst e2)
-- | (exp.if_then_else e1 e2 e3) :=
--   exp.if_then_else (subst e1) (subst e2) (subst e3)
-- | (exp.let_in ty e1 e2) := exp.let_in ty (subst e1) (subst e2)
-- | (exp.ignore e1 e2) := exp.ignore (subst e1) (subst e2)
-- | (exp.let_app ty f e1 e2) := exp.let_app ty f (subst e1) (subst e2)
-- | (exp.let_newbuf n e1 ty e2) := exp.let_newbuf n (subst e1) ty (subst e2)
-- | (exp.let_readbuf ty e1 e2 e3) :=
--   exp.let_readbuf ty (subst e1) (subst e2) (subst e3)
-- | (exp.writebuf e1 e2 e3 e4) :=
--   exp.writebuf (subst e1) (subst e2) (subst e3) (subst e4)
-- | (exp.let_newstruct e1 ty e2) := exp.let_newstruct (subst e1) ty (subst e2)
-- | (exp.let_readstruct ty e1 e2) := exp.let_readstruct ty (subst e1) (subst e2)
-- | (exp.writestruct e1 e2) := exp.writestruct (subst e1) (subst e2)
-- | (exp.withframe e) := exp.withframe (subst e)
-- | (exp.pop e) := exp.pop (subst e)
-- | e := e

-- def open_aux (u : exp) : nat → exp → exp
-- | k (exp.bvar i) :=
--   if i = k then u else (exp.bvar i)
-- | k (exp.fvar y) :=
--   exp.fvar y
-- --| k (exp.struct s) := sorry
-- | k (exp.field e fd) :=
--   exp.field (open_aux k e) fd
-- | k (exp.mut_field e fd) :=
--   exp.mut_field (open_aux k e) fd
-- | k (exp.subbuf e1 e2) :=
--   exp.subbuf (open_aux k e1) (open_aux k e2)
-- | k (exp.if_then_else e1 e2 e3) :=
--   exp.if_then_else (open_aux k e1) (open_aux k e2) (open_aux k e3)
-- | k (exp.let_in ty e1 e2) :=
--   exp.let_in ty (open_aux k e1) (open_aux (nat.succ k) e2)
-- | k (exp.ignore e1 e2) :=
--   exp.ignore (open_aux k e1) (open_aux k e2)
-- | k (exp.let_app ty f e1 e2) :=
--   exp.let_app ty f (open_aux k e1) (open_aux (nat.succ k) e2)
-- | k (exp.let_newbuf n e1 ty e2) :=
--   exp.let_newbuf n (open_aux k e1) ty (open_aux (nat.succ k) e2)
-- | k (exp.let_readbuf ty e1 e2 e3) :=
--   exp.let_readbuf ty (open_aux k e1) (open_aux k e2) (open_aux (nat.succ k) e3)
-- | k (exp.writebuf e1 e2 e3 e4) :=
--   exp.writebuf (open_aux k e1) (open_aux k e2) (open_aux k e3) (open_aux (nat.succ k) e4)
-- | k (exp.let_newstruct e1 ty e2) :=
--   exp.let_newstruct (open_aux k e1) ty (open_aux (nat.succ k) e2)
-- | k (exp.let_readstruct ty e1 e2) :=
--   exp.let_readstruct ty (open_aux k e1) (open_aux (nat.succ k) e2)
-- | k (exp.writestruct e1 e2) :=
--   exp.writestruct (open_aux k e1) (open_aux k e2)
-- | k (exp.withframe e) :=
--   exp.withframe (open_aux k e)
-- | k (exp.pop e) :=
--   exp.pop (open_aux k e)
-- | k e := e

-- def opening (e : exp) (u : exp) : exp :=
--   open_aux u 0 e

end lowstar
