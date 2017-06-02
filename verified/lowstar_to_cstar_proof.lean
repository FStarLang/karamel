import lowstar_to_cstar
import lowstar_semantics
import cstar_semantics
import lowstar_to_cstar -- for transl_typ (FIXME?)
import transition

namespace lowstar_to_cstar_proof

open common
open semantics_common
open lowstar
open cstar
open lowstar_semantics
open cstar_semantics
open lowstar_to_cstar

universe variable u

-- C* to λow* back-translation

inductive back_exp {X : Type u} :
  (X → ident) → cstar.exp → lowstar.exp X → Prop
| int : ∀ names n,
  back_exp names (exp.int n) (exp.int n)
| unit : ∀ names,
  back_exp names exp.unit exp.unit
| loc : ∀ names l,
  back_exp names (exp.loc l) (exp.loc l)
| ptr_add : ∀ names e₁ e₂ le₁ le₂,
  back_exp names e₁ le₁ →
  back_exp names e₂ le₂ →
  back_exp names (exp.ptr_add e₁ e₂) (exp.subbuf le₁ le₂)
-- struct, field, field_addr
| var : ∀ names (x : X), -- ?
  back_exp names (exp.var (names x)) (exp.var x)

inductive back_stmt : ∀ {X : Type u},
  (X → ident) → list cstar.stmt → lowstar.exp X → Prop
| let_in : ∀ X (names : X → ident) b e ss τ (le1 : exp X) (le : exp (^X)),
  back_exp names e le1 →
  back_stmt (names_cons (binder.name b) names) ss le →
  transl_typ τ = binder.typ b → -- ehh
  back_stmt names
    ((stmt.decl b e) :: ss)
    (exp.let_in τ le1 le)
| let_newbuf : ∀ X (names : X → ident) x b n ss τ e le1 le,
  back_exp names e le1 →
  x = binder.name b →
  back_stmt (names_cons x names) ss le →
  transl_typ τ = binder.typ b → -- ehh
  back_stmt names
    ((stmt.decl_buf b n) :: (stmt.write_buf (exp.var x) n e) :: ss)
    (exp.let_newbuf n le1 τ le)
| let_app : ∀ X (names : X → ident) b x τ fn e ss le1 le,
  back_exp names e le1 →
  x = binder.name b →
  transl_typ τ = binder.typ b → -- ehh
  back_stmt (names_cons x names) ss le →
  back_stmt names
    ((stmt.call b fn e) :: ss)
    (exp.let_app τ fn le1 le)
| let_readbuf : ∀ X (names : X → ident) b x τ e1 e2 ss le1 le2 le,
  back_exp names e1 le1 →
  back_exp names e2 le2 →
  x = binder.name b →
  transl_typ τ = binder.typ b → -- ehh
  back_stmt (names_cons x names) ss le →
  back_stmt names
    ((stmt.read b (exp.ptr_add e1 e2)) :: ss)
    (exp.let_readbuf τ le1 le2 le)
| writebuf : ∀ X (names : X → ident) e1 e2 e3 ss le1 le2 le3 le,
  back_exp names e1 le1 →
  back_exp names e2 le2 →
  back_exp names e3 le3 →
  back_stmt names ss le →
  back_stmt names
    ((stmt.write (exp.ptr_add e1 e2) e3) :: ss)
    (exp.writebuf le1 le2 le3 le)
| withframe : ∀ X (names : X → ident) ss1 ss le1 le,
  back_stmt names ss1 le1 →
  back_stmt names ss le →
  back_stmt names
    ((stmt.block ss1) :: ss)
    (exp.ignore (exp.withframe le1) le)
| ignore : ∀ X (names : X → ident) e1 ss le1 le,
  back_exp names e1 le1 →
  back_stmt names ss le →
  back_stmt names
    ((stmt.ignore e1) :: ss)
    (exp.ignore le1 le)
| if_then_else : ∀ X (names : X → ident) e ss1 ss2 ss3 le le1 le2 le3,
  back_exp names e le →
  back_stmt names ss1 le1 →
  back_stmt names ss2 le2 →
  back_stmt names ss3 le3 →
  back_stmt names
    ((stmt.if_then_else e ss1 ss2) :: ss3)
    (exp.ignore (exp.if_then_else le le1 le2) le3)
| exp : ∀ X (names : X → ident) e le,
  back_exp names e le →
  back_stmt names [stmt.return e] le
| unit : ∀ X (names : X → ident),
  back_stmt names [] exp.unit

inductive back_decl : cstar.decl → lowstar.decl → Prop
| function : ∀ ret_ty fn x b ss τ ρ e (le : exp (^pempty.{u})),
  x = binder.name b →
  transl_typ τ = binder.typ b → -- ehh
  transl_typ ρ = ret_ty →
  back_stmt (names_cons x names_empty) (ss ++ [stmt.ignore e]) le → -- ?
  back_decl
    (decl.function ret_ty fn b (ss ++ [stmt.return e])) -- ?
    (decl.function fn ρ le τ)

inductive back_ectx : ∀ {X : Type u} (names : X → ident),
  cstar_semantics.ectx → lowstar_semantics.ectx X → Prop
| ignore : ∀ X (names : X → ident) ss le,
  back_stmt names ss le →
  back_ectx names (ectx.ignore ss) (ectx.ignore ectx.here le)
| read : ∀ X (names : X → ident) ss le b x τ,
  x = binder.name b →
  transl_typ τ = binder.typ b → -- ehh
  back_stmt (names_cons x names) ss le →
  back_ectx names (ectx.read b ss) (ectx.let_in τ ectx.here le)

-- transition systems

def sys_cstar
  (p : cstar.program) (V : vars) (ss : list stmt) :
  transition.system label
:=
  transition.system.mk
    cstar_semantics.configuration
    (cstar_semantics.step p)
    ([], V, ss)
    (λC, let (stk, _, ss) := C in stk = [] ∧ ∃ e, ss = [stmt.return e])

def sys_lowstar
  {X : Type u} (lp : lowstar.program) (le : exp X) :
  transition.system label
:=
  transition.system.mk
    (lowstar_semantics.configuration X)
    (lowstar_semantics.step lp)
    (([] : lowstar_semantics.stack), le)
    (λC, let (stk, le) := C in stk = [] ∧ ∃ lv, le = exp_of_value lv)

-- rel

def close_vars
  {X : Type u} (names : X → ident) (V : vars) (e : exp X) :
  exp X
:=
  exp_bind e (λ (x : X),
    match V (names x) with
    | none := exp.var x
    | some v := v
    end)

def ectx_close_vars
  {X : Type u} (names : X → ident) (V : vars) (c : ectx X) :
  ectx X
:=
  ectx_bind c (λ (x : X),
    match V (names x) with
    | none := exp.var x
    | some v := v
    end)

def mem : cstar_semantics.stack → lowstar_semantics.stack :=
  sorry
  -- TODO


inductive unravel_frame {X : Type u} (names : X → ident) :
  exp X → cstar_semantics.frame → exp X → Prop
| no_mem : ∀ V E lE le,
  back_ectx names E lE →
  unravel_frame
    le (none, V, E)
    (close_vars names V (apply_ectx lE le))
| mem : ∀ M V E lE le,
  back_ectx names E lE →
  unravel_frame
    le (some M, V, E)
    (close_vars names V (apply_ectx lE (exp.pop le)))

inductive unravel {X : Type u} (names : X → ident) :
  cstar_semantics.stack → exp X → exp X → Prop
| nil : ∀ le,
  unravel [] le le
| cons : ∀ le le' le'' F FS,
  unravel_frame names le F le' →
  unravel FS le' le'' →
  unravel (F :: FS) le le''

--TODO: move
inductive back_cfg {X : Type u} (names : X → ident) (p : cstar.program) :
  cstar_semantics.configuration → lowstar_semantics.configuration X → Prop
| mk : ∀ S V ss ss' le le',
  eval_head_exp p V ss ss' →
  back_stmt names ss' le →
  unravel names S (close_vars names V le) le' →
  back_cfg (S, V, ss) (mem S, le')

def rel {X : Type u}
  (p : cstar.program) (lp : lowstar.program)
  (names : X → ident)
  (lC : lowstar_semantics.configuration X)
  (C : cstar_semantics.configuration) :
  Prop
:=
  let (H, le) := lC in
  ∃ (n : nat) (le' : exp X),
  back_cfg names p C (H, le') ∧
  (transition.iter (lowstar_semantics.step lp) n) (H, le) (H, le') [] --?

-- auxiliary lemmas

lemma back_stmt_value {X : Type u} (le : exp X) (v : value) : ∀ names,
  back_stmt names [stmt.return v] le →
  le = v
:=
begin
  intros _ H,
  cases v; cases H,
  { cases a_1, refl },
  { cases a, refl },
  { cases a_1, refl }
end

lemma close_vars_value (v : value) : ∀ {X : Type u} (names : X → ident) V,
  close_vars names V v = v
:=
begin
  introv, cases v; simp [close_vars];
  unfold coe lift_t has_lift_t.lift coe_t has_coe_t.coe coe_b has_coe.coe; -- ??
  simp [lowstar.exp_of_value]; simp [exp_bind]
end

end lowstar_to_cstar_proof
