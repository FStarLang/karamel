import lowstar_to_cstar
import lowstar_semantics
import cstar_semantics
import lowstar_to_cstar -- for transl_typ (FIXME?)

namespace lowstar_to_cstar_proof

open common
open lowstar
open cstar
open lowstar_semantics
open cstar_semantics
open lowstar_to_cstar

universe variable u

-- C* to λow* back-translation

inductive back_exp {X : Type u} :
  (X → ident) → cstar.exp → lowstar.exp X → Type (u+1)
| int : ∀ names n,
  back_exp names (exp.int n) (exp.int n)
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
  (X → ident) → list cstar.stmt → lowstar.exp X → Type (u+1)
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
  back_stmt names [stmt.ignore e] le
| unit : ∀ X (names : X → ident),
  back_stmt names [] exp.unit

inductive back_decl : cstar.decl → lowstar.decl → Type
| function : ∀ ret_ty fn x b ss τ ρ e le,
  x = binder.name b →
  transl_typ τ = binder.typ b → -- ehh
  transl_typ ρ = ret_ty →
  back_stmt (names_cons x names_empty) (ss ++ [stmt.ignore e]) le → -- ?
  back_decl
    (decl.function ret_ty fn b (ss ++ [stmt.return e])) -- ?
    (


end lowstar_to_cstar_proof
