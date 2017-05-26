import lowstar
import semantics_common

namespace lowstar_semantics

open common
open semantics_common
open lowstar

-- λow* semantics definitions

universe variable u

inductive ectx : Type u → Type (u+1)
| here : ∀ {X}, ectx X
-- | field : ectx → common.field → ectx
-- | mut_field : ectx → common.field → ectx
-- | struct :
--   list (common.field × value) →
--   common.field → ectx →
--   list (field × lowstar.exp) →
--   ectx
| subbuf_1 : ∀ {X}, ectx X → lowstar.exp X → ectx X
| subbuf_2 : ∀ {X}, value → ectx X → ectx X
| if_then_else : ∀ {X}, ectx X → lowstar.exp X → lowstar.exp X → ectx X
| let_in : ∀ {X}, typ → ectx X → lowstar.exp (^X) → ectx X
| ignore : ∀ {X}, ectx X → lowstar.exp X → ectx X
| let_app : ∀ {X}, typ → glob → ectx X → lowstar.exp (^X) → ectx X
| let_newbuf : ∀ {X}, nat → ectx X → typ → lowstar.exp (^X) → ectx X
| let_readbuf_1 : ∀ {X}, typ → ectx X → lowstar.exp X → lowstar.exp (^X) → ectx X
| let_readbuf_2 : ∀ {X}, typ → value → ectx X → lowstar.exp (^X) → ectx X
| writebuf_1 : ∀ {X}, ectx X → lowstar.exp X → lowstar.exp X → lowstar.exp X → ectx X
| writebuf_2 : ∀ {X}, value → ectx X → lowstar.exp X → lowstar.exp X → ectx X
| writebuf_3 : ∀ {X}, value → value → ectx X → lowstar.exp X → ectx X
-- | let_newstruct : ectx → typ → lowstar.exp → ectx
-- | let_readstruct : typ → ectx → lowstar.exp → ectx
-- | write_struct_1 : ectx → lowstar.exp → lowstar.exp → ectx
-- | write_struct_2 : value → ectx → lowstar.exp → ectx
| pop : ∀ {X}, ectx X → ectx X


def frame : Type :=
  map block_id (list value)

def stack : Type :=
  list frame

def configuration (X : Type u) : Type (u+1) :=
  stack × lowstar.exp X

-- λow* atomic reduction rules
-- Small-step semantics

def stack_read_loc (l : location) : stack → option value :=
  sorry

def stack_write_loc (l : location) (v : value) : stack → stack :=
  sorry

def block_free_in_stack (b : block_id) (s : stack) : Prop :=
  sorry

inductive astep {X : Type u} (gvars : glob → option decl) :
  configuration X → configuration X → list label → Type (u+1)
| readbuf : ∀ stack ty b n n' e v,
  stack_read_loc (b, n + n', []) stack = some v →
  astep
    (stack, exp.let_readbuf ty (exp.loc (b,n,[])) (exp.int n') e)
    (stack, e ← v)
    [label.read (b, n+n', [])]
--| readstruct
| let_app : ∀ stack ty f param_ty ret_ty f_body (v : value) e,
  gvars f = some (decl.function f param_ty f_body ret_ty) →
  astep
    (stack, exp.let_app ty f v e)
    (stack, exp.let_in ty ((f_body X) ← v) e)
    []
| writebuf : ∀ stack b n n' oldv (v : value) e,
  stack_read_loc (b, n + n', []) stack = oldv →
  astep
    (stack, exp.writebuf (exp.loc (b,n,[])) (exp.int n') v e)
    (stack_write_loc (b,n+n',[]) v stack, e)
    [label.write (b, n + n', [])]
--| writestruct
| subbuf : ∀ stack b n n',
  astep
    (stack, exp.subbuf (exp.loc (b,n,[])) (exp.int n'))
    (stack, exp.loc (b, n + n', []))
    []
--| structfield
| let_in : ∀ stack ty (v : value) e,
  astep
    (stack, exp.let_in ty v e)
    (stack, e ← v)
    []
| ignore : ∀ stack (v : value) e,
  astep
    (stack, exp.ignore v e)
    (stack, e)
    []
--| field
| if_true : ∀ stack n e1 e2,
  ¬ (n = 0) →
  astep
    (stack, exp.if_then_else (exp.int n) e1 e2)
    (stack, e1)
    [label.branch_true]
| if_false : ∀ stack n e1 e2,
  n = 0 →
  astep
    (stack, exp.if_then_else (exp.int n) e1 e2)
    (stack, e2)
    [label.branch_false]
| newbuf : ∀ stack new_frame b n (v : value) ty e,
  block_free_in_stack b stack →
  new_frame = map_singleton b (list.repeat v n) →
  astep
    (stack, exp.let_newbuf n v ty e)
    (new_frame :: stack, e ← (exp.loc (b, 0, [])))
    (memset_labels b 0 n)
--| newstruct
| withframe : ∀ stack e,
  astep
    (stack, exp.withframe e)
    (map_empty :: stack, exp.pop e)
    []
| pop : ∀ stack frame (v : value),
  astep
    (frame :: stack, exp.pop v)
    (stack, v)
    []

-- λow* reduction rule(s)
-- Small-step semantics

def apply_ectx : ∀ {X : Type u}, ectx X → lowstar.exp X → lowstar.exp X
| X ectx.here e := e
| X (ectx.subbuf_1 ctx e2) e :=
  exp.subbuf (apply_ectx ctx e) e2
| X (ectx.subbuf_2 v ctx) e :=
  exp.subbuf v (apply_ectx ctx e)
| X (ectx.if_then_else ctx e1 e2) e :=
  exp.if_then_else (apply_ectx ctx e) e1 e2
| X (ectx.let_in ty ctx e1) e :=
  exp.let_in ty (apply_ectx ctx e) e1
| X (ectx.ignore ctx e1) e :=
  exp.ignore (apply_ectx ctx e) e1
| X (ectx.let_app ty f ctx e1) e :=
  exp.let_app ty f (apply_ectx ctx e) e1
| X (ectx.let_newbuf n ctx ty e1) e :=
  exp.let_newbuf n (apply_ectx ctx e) ty e1
| X (ectx.let_readbuf_1 ty ctx e1 e2) e :=
  exp.let_readbuf ty (apply_ectx ctx e) e1 e2
| X (ectx.let_readbuf_2 ty v ctx e1) e :=
  exp.let_readbuf ty v (apply_ectx ctx e) e1
| X (ectx.writebuf_1 ctx e1 e2 e3) e :=
  exp.writebuf (apply_ectx ctx e) e1 e2 e3
| X (ectx.writebuf_2 v ctx e1 e2) e :=
  exp.writebuf v (apply_ectx ctx e) e1 e2
| X (ectx.writebuf_3 v1 v2 ctx e1) e :=
  exp.writebuf v1 v2 (apply_ectx ctx e) e1
| X (ectx.pop ctx) e :=
  exp.pop (apply_ectx ctx e)

inductive step {X : Type u} (gvars : glob → option decl) :
  configuration X → configuration X → list label → Type (u+1)
| step : ∀ stack stack' e e' ctx lbls,
  astep gvars (stack, e) (stack', e') lbls →
  step (stack, apply_ectx ctx e) (stack', apply_ectx ctx e') lbls

end lowstar_semantics
