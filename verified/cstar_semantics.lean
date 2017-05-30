import cstar
-- import data.hash_map
import semantics_common

namespace cstar_semantics

open common
open semantics_common
open cstar

-- Semantics definitions

inductive ectx : Type
| ignore : list stmt → ectx
| read : binder → list stmt → ectx

def memory : Type :=
  map block_id (list (option value))

def vars : Type :=
  map ident value

def frame : Type :=
  option memory × vars × ectx

def stack : Type :=
  list frame

def configuration : Type :=
  stack × vars × list stmt

-- Auxiliary definitions

def apply_ectx (c : ectx) (e : cstar.exp) : list stmt :=
  match c with
  | ectx.ignore ss := (stmt.ignore e) :: ss
  | ectx.read b ss := (stmt.read b e) :: ss
  end

-- instance : decidable_eq cstar.field :=
-- by { unfold cstar.field, apply_instance }

def get_field {α} (fd : common.field) : (list (field × α)) → option α
| [] := none
| ((fd', v) :: fds) :=
  if fd = fd' then some v
  else get_field fds

-- C* expession evaluation
-- Big-step semantics: expessions are pure, and reducing does not change the
-- trace

inductive eval_exp
  (gvars : map glob decl) (vars : map ident value) :
  cstar.exp → value → Prop
| var : ∀ x v,
  vars x = some v →
  eval_exp (cstar.exp.var x) v
| ptr_add : ∀ e₁ e₂ b n n',
  eval_exp e₁ (value.loc (b, n, [])) →
  eval_exp e₂ (value.int n') →
  eval_exp (cstar.exp.ptr_add e₁ e₂) (value.loc (b, n + n', []))
| field_addr : ∀ e fd fds b n,
  eval_exp e (value.loc (b, n, fds)) →
  eval_exp (cstar.exp.field_addr e fd) (value.loc (b, n, fd :: fds))
-- TODO: struct
-- | field : ∀ e fd s v,
--   eval_exp e (value.struct s) →
--   get_field fd s = some v →
--   eval_exp (cstar.exp.field e fd) v

-- C* head expression evaluation

inductive eval_head_exp
  (gvars : map glob decl) (vars : map ident value) :
  list cstar.stmt → list cstar.stmt → Prop
| decl : ∀ b e v ss,
  eval_exp gvars vars e v →
  eval_head_exp (stmt.decl b e :: ss) (stmt.decl b v :: ss)
| decl_buf : ∀ b n ss,
  eval_head_exp (stmt.decl_buf b n :: ss) (stmt.decl_buf b n :: ss)
| write_buf : ∀ e₁ n e₂ v₁ v₂ ss,
  eval_exp gvars vars e₁ v₁ →
  eval_exp gvars vars e₂ v₂ →
  eval_head_exp (stmt.write_buf e₁ n e₂ :: ss) (stmt.write_buf v₁ n v₂ :: ss)
| call : ∀ x fn e v ss,
  eval_exp gvars vars e v →
  eval_head_exp (stmt.call x fn e :: ss) (stmt.call x fn v :: ss)
| read : ∀ x e v ss, -- ?
  eval_exp gvars vars e v →
  eval_head_exp (stmt.read x e :: ss) (stmt.read x v :: ss)
| write : ∀ e₁ e₂ v₁ v₂ ss, -- ?
  eval_exp gvars vars e₁ v₁ →
  eval_exp gvars vars e₂ v₂ →
  eval_head_exp (stmt.write e₁ e₂ :: ss) (stmt.write v₁ v₂ :: ss)
| ignore : ∀ e v ss,
  eval_exp gvars vars e v →
  eval_head_exp (stmt.ignore e :: ss) (stmt.ignore v :: ss)
| return : ∀ e v ss,
  eval_exp gvars vars e v →
  eval_head_exp (stmt.return e :: ss) (stmt.return v :: ss)

-- C* configuration reduction
-- Small-step semantics

-- placeholders
def bind_in (vars : map ident value) (binder : binder) (v : value) : map ident value :=
  sorry

def block_id_free_in_stack (b : block_id) (s : stack) : bool :=
  sorry

def stack_memset (s : stack) (l : location) (v : value) (n : nat) : stack :=
  sorry

def stack_get (s : stack) (l : location) : option value :=
  sorry

def stack_set (s : stack) (l : location) (v : value) : stack :=
  sorry

inductive step (gvars : map glob decl) :
  configuration → configuration → list label → Prop
| decl : ∀ stack vars bind e ss v,
  eval_exp gvars vars e v →
  step
    (stack, vars, (stmt.decl bind e) :: ss)
    (stack, bind_in vars bind v, ss)
    []
| decl_buf : ∀ stack stack' mem vars vars' ctx bind n ss b buf new_frame,
  stack = (some mem, vars, ctx) :: stack' →
  block_id_free_in_stack b stack = true →
  buf = @list.repeat (option value) none n →
  new_frame = (some (map_add mem b buf), vars, ctx) →
  vars' = bind_in vars bind (value.loc (b, 0, [])) →
  step
    (stack, vars, (stmt.decl_buf bind n) :: ss)
    (new_frame :: stack', vars', ss)
    []
| write_buf : ∀ stack stack' vars m n b e₁ e₂ v ss,
  eval_exp gvars vars e₁ (value.loc (b, n, [])) →
  eval_exp gvars vars e₂ v →
  stack_memset stack (b, n, []) v m = stack' →
  step
    (stack, vars, (stmt.write_buf e₁ m e₂) :: ss)
    (stack', vars, ss)
    (memset_labels b n m)
| read : ∀ stack vars vars' b loc e v ss,
  eval_exp gvars vars e (value.loc loc) →
  stack_get stack loc = some v →
  vars' = map_add vars (binder.name b) v →
  step
    (stack, vars, (stmt.read b e) :: ss)
    (stack, vars', ss)
    [label.read loc]
| write : ∀ stack stack' vars e₁ e₂ loc v ss,
  eval_exp gvars vars e₁ (value.loc loc) →
  eval_exp gvars vars e₂ v →
  stack_set stack loc v = stack' →
  step
    (stack, vars, (stmt.write e₁ e₂) :: ss)
    (stack', vars, ss)
    [label.write loc]
| return : ∀ stack vars vars' ctx e v ss,
  eval_exp gvars vars e v →
  step
    ((none, vars', ctx) :: stack, vars, (stmt.return e) :: ss)
    (stack, vars', apply_ectx ctx v)
    []
| return_block : ∀ stack mem vars vars' ctx e v ss,
  eval_exp gvars vars e v →
  step
    ((mem, vars', ctx) :: stack, vars, (stmt.return e) :: ss)
    (stack, map_empty, [stmt.return v])
    []
| call : ∀ stack vars vars' b f f_ret_ty f_param f_body e v ss,
  gvars f = some (decl.function f_ret_ty f f_param f_body) →
  eval_exp gvars vars e v →
  vars' = bind_in vars f_param v →
  step
    (stack, vars, (stmt.call b f e) :: ss)
    ((none, vars, ectx.read b ss) :: stack, vars', f_body)
    []
| ignore : ∀ stack vars e v ss,
  eval_exp gvars vars e v →
  step
    (stack, vars, (stmt.ignore e) :: ss)
    (stack, vars, ss)
    []
| empty : ∀ stack mem vars vars' ctx,
  step
    ((mem, vars', ctx) :: stack, vars, [])
    (stack, vars', apply_ectx ctx exp.unit)
    []
| block : ∀ stack vars ss₁ ss₂,
  step
    (stack, vars, (stmt.block ss₁) :: ss₂)
    ((some map_empty, vars, ectx.ignore ss₂) :: stack, vars, ss₁)
    []
| if_true : ∀ stack vars e n ss1 ss2 ss,
  eval_exp gvars vars e (value.int n) →
  ¬ (n = 0) →
  step
    (stack, vars, (stmt.if_then_else e ss1 ss2) :: ss)
    (stack, vars, ss1 ++ ss)
    [label.branch_true]
| if_false : ∀ stack vars e n ss1 ss2 ss,
  eval_exp gvars vars e (value.int n) →
  n = 0 →
  step
    (stack, vars, (stmt.if_then_else e ss1 ss2) :: ss)
    (stack, vars, ss2 ++ ss)
    [label.branch_false]

end cstar_semantics
