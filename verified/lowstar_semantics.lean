import lowstar
import semantics_common
import transition

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

def ectx_map : ∀ {X Y : Type u} (f : X → Y), ectx X → ectx Y
| X Y f ectx.here := ectx.here
| X Y f (ectx.subbuf_1 c e) := ectx.subbuf_1 (ectx_map f c) (exp_map f e)
| X Y f (ectx.subbuf_2 v c) := ectx.subbuf_2 v (ectx_map f c)
| X Y f (ectx.if_then_else c e1 e2) := ectx.if_then_else (ectx_map f c) (exp_map f e1) (exp_map f e2)
| X Y f (ectx.let_in τ c e) := ectx.let_in τ (ectx_map f c) (exp_map (^^f) e)
| X Y f (ectx.ignore c e) := ectx.ignore (ectx_map f c) (exp_map f e)
| X Y f (ectx.let_app τ fn c e) := ectx.let_app τ fn (ectx_map f c) (exp_map (^^f) e)
| X Y f (ectx.let_newbuf n c τ e) := ectx.let_newbuf n (ectx_map f c) τ (exp_map (^^f) e)
| X Y f (ectx.let_readbuf_1 τ c e1 e2) := ectx.let_readbuf_1 τ (ectx_map f c) (exp_map f e1) (exp_map (^^f) e2)
| X Y f (ectx.let_readbuf_2 τ v c e) := ectx.let_readbuf_2 τ v (ectx_map f c) (exp_map (^^f) e)
| X Y f (ectx.writebuf_1 c e1 e2 e3) := ectx.writebuf_1 (ectx_map f c) (exp_map f e1) (exp_map f e2) (exp_map f e3)
| X Y f (ectx.writebuf_2 v c e1 e2) := ectx.writebuf_2 v (ectx_map f c) (exp_map f e1) (exp_map f e2)
| X Y f (ectx.writebuf_3 v1 v2 c e) := ectx.writebuf_3 v1 v2 (ectx_map f c) (exp_map f e)
| X Y f (ectx.pop c) := ectx.pop (ectx_map f c)

def ectx_bind : ∀ {X Y : Type u}, ectx X → (X → exp Y) → ectx Y
| X Y ectx.here f := ectx.here
| X Y (ectx.subbuf_1 c e) f := ectx.subbuf_1 (ectx_bind c f) (exp_bind e f)
| X Y (ectx.subbuf_2 v c) f := ectx.subbuf_2 v (ectx_bind c f)
| X Y (ectx.if_then_else c e1 e2) f := ectx.if_then_else (ectx_bind c f) (exp_bind e1 f) (exp_bind e2 f)
| X Y (ectx.let_in τ c e) f := ectx.let_in τ (ectx_bind c f) (exp_bind e (f_lift f))
| X Y (ectx.ignore c e) f := ectx.ignore (ectx_bind c f) (exp_bind e f)
| X Y (ectx.let_app τ fn c e) f := ectx.let_app τ fn (ectx_bind c f) (exp_bind e (f_lift f))
| X Y (ectx.let_newbuf n c τ e) f := ectx.let_newbuf n (ectx_bind c f) τ (exp_bind e (f_lift f))
| X Y (ectx.let_readbuf_1 τ c e1 e2) f := ectx.let_readbuf_1 τ (ectx_bind c f) (exp_bind e1 f) (exp_bind e2 (f_lift f))
| X Y (ectx.let_readbuf_2 τ v c e) f := ectx.let_readbuf_2 τ v (ectx_bind c f) (exp_bind e (f_lift f))
| X Y (ectx.writebuf_1 c e1 e2 e3) f := ectx.writebuf_1 (ectx_bind c f) (exp_bind e1 f) (exp_bind e2 f) (exp_bind e3 f)
| X Y (ectx.writebuf_2 v c e1 e2) f := ectx.writebuf_2 v (ectx_bind c f) (exp_bind e1 f) (exp_bind e2 f)
| X Y (ectx.writebuf_3 v1 v2 c e) f := ectx.writebuf_3 v1 v2 (ectx_bind c f) (exp_bind e f)
| X Y (ectx.pop c) f := ectx.pop (ectx_bind c f)

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

inductive astep {X : Type u} (decls : list decl) :
  configuration X → configuration X → list label → Prop
| readbuf : ∀ stack ty b n n' e v,
  stack_read_loc (b, n + n', []) stack = some v →
  astep
    (stack, exp.let_readbuf ty (exp.loc (b,n,[])) (exp.int n') e)
    (stack, e ◄ v)
    [label.read (b, n+n', [])]
--| readstruct
| let_app : ∀ stack ty f param_ty ret_ty f_body (v : value) e,
  find_fundecl f decls = some (decl.function f param_ty f_body ret_ty) →
  astep
    (stack, exp.let_app ty f v e)
    (stack, exp.let_in ty ((lift_fbody X f_body) ◄ v) e)
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
    (stack, e ◄ v)
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
    (new_frame :: stack, e ◄ (exp.loc (b, 0, [])))
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

inductive step {X : Type u} (decls : list decl) :
  configuration X → configuration X → list label → Prop
| step : ∀ stack stack' e e' ctx lbls,
  astep decls (stack, e) (stack', e') lbls →
  step (stack, apply_ectx ctx e) (stack', apply_ectx ctx e') lbls

section
open transition

lemma step_steps_aux : ∀ {X : Type u} (decls : list decl) stack stack' (e e' : exp X) ctx ls cfg cfg',
  cfg = (stack, e) →
  cfg' = (stack', e') →
  star (step decls) cfg cfg' ls →
  star (step decls) (stack, apply_ectx ctx e) (stack', apply_ectx ctx e') ls
:=
begin
  introv C1 C2 S, revert stack stack' e e', induction S with cfg cfg cfg' cfg'' _ _ S SS,
  { intros, subst C1, injection C2 with h h', subst h, subst h', constructor }, -- meh
  { intros, subst C1, subst C2, cases cfg' with stack1 e1, cases S, /- boom -/
    admit
  }
end

--ehhh
lemma step_steps : ∀ {X : Type u} (decls : list decl) stack stack' (e e' : exp X) ctx ls,
  star (step decls) (stack, e) (stack', e') ls →
  star (step decls) (stack, apply_ectx ctx e) (stack', apply_ectx ctx e') ls
:=
begin
  intros,
  apply step_steps_aux; [reflexivity, reflexivity, assumption]
end

end

end lowstar_semantics
