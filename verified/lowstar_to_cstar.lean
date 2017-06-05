import lowstar
import cstar
import data.set

namespace lowstar_to_cstar

open common
open lowstar
open cstar

-- Translation of λow* types

def flatten_arrow_aux :
  list lowstar.typ →
  lowstar.typ →
  lowstar.typ × list lowstar.typ
| acc (typ.arrow τ₁ τ₂) := flatten_arrow_aux (τ₁ :: acc) τ₂
| acc τ := (τ, list.reverse acc)

def flatten_arrow : lowstar.typ → lowstar.typ × list lowstar.typ :=
  flatten_arrow_aux []

-- in λow*, buf vs array?
def transl_typ : lowstar.typ → cstar.typ
| typ.int := typ.int
| typ.unit := typ.pointer typ.void
| (typ.buf τ) := typ.pointer (transl_typ τ)
-- | (typ.arrow τ₁ τ₂) :=
--   let (ret, args) := flatten_arrow (typ.arrow τ₁ τ₂) in
--   typ.function (transl_typ ret) (list.map transl_typ args)

-- placeholder implementation
| (typ.arrow τ₁ τ₂) := typ.function (transl_typ τ₂) [transl_typ τ₁]

-- Translation of λow* expressions

def transl_to_exp : ∀ {X}, (X → ident) → lowstar.exp X → option cstar.exp
| X names (exp.int n) := some (exp.int n)
| X names exp.unit := some (exp.unit)
| X names (exp.loc l) := some (exp.loc l)
| X names (exp.var x) := some (exp.var (names x))
--| struct
| X names (exp.subbuf e1 e2) := do
  ce1 ← transl_to_exp names e1,
  ce2 ← transl_to_exp names e2,
  some (exp.ptr_add ce1 ce2)
--| field
--| field_mut
| X names _ := none

def transl_to_stmt : ∀ {X},
  idents → (X → ident) →
  lowstar.exp X →
  option (idents × list cstar.stmt)
| X seen names (exp.if_then_else e1 e2 e3) := do
  ce1 ← transl_to_exp names e1,
  (seen2, ss2) ← transl_to_stmt seen names e2,
  (seen3, ss3) ← transl_to_stmt seen2 names e3,
  some (seen3, [stmt.if_then_else ce1 ss2 ss3])

| X seen names (exp.let_in τ e1 e) :=
  let id := fresh_ident seen in do
  ce1 ← transl_to_exp names e1,
  (seen', ss) ← transl_to_stmt (set.insert id seen) (names_cons id names) e,
  some (seen', (stmt.decl (binder.mk id (transl_typ τ)) ce1) :: ss)

| X seen names (exp.ignore e1 e) := do
  ce1 ← transl_to_exp names e1,
  (seen', ss) ← transl_to_stmt seen names e,
  some (seen', (stmt.ignore ce1) :: ss)

| X seen names (exp.let_app τ fn e1 e) :=
  let id := fresh_ident seen in
  let τ' := transl_typ τ in do
  ce1 ← transl_to_exp names e1,
  (seen', ss) ← transl_to_stmt (set.insert id seen) (names_cons id names) e,
  some (seen', (stmt.call (binder.mk id τ') fn ce1) :: ss)

| X seen names (exp.let_newbuf size e1 τ e) :=
  let id := fresh_ident seen in do
  ce1 ← transl_to_exp names e1,
  (seen', ss) ← transl_to_stmt (set.insert id seen) (names_cons id names) e,
  some (seen',
        (stmt.decl_buf (binder.mk id (transl_typ τ)) size) ::
        (stmt.write_buf (exp.var id) size ce1) ::
        ss)

| X seen names (exp.let_readbuf τ e1 e2 e) :=
  let id := fresh_ident seen in
  let τ' := transl_typ τ in do
  ce1 ← transl_to_exp names e1,
  ce2 ← transl_to_exp names e2,
  (seen', ss) ← transl_to_stmt (set.insert id seen) (names_cons id names) e,
  some (seen', (stmt.read (binder.mk id τ') (exp.ptr_add ce1 ce2)) :: ss)

| X seen names (exp.writebuf e1 e2 e3 e) := do
  ce1 ← transl_to_exp names e1,
  ce2 ← transl_to_exp names e2,
  ce3 ← transl_to_exp names e3,
  (seen', ss) ← transl_to_stmt seen names e,
  some (seen', (stmt.write (exp.ptr_add ce1 ce2) ce3) :: ss)

| X seen names (exp.withframe e) := do
  (seen', ss) ← transl_to_stmt seen names e,
  some (seen', [stmt.block ss])

| X seen names (exp.pop _) :=
  none

| X seen names e := do
  ce ← transl_to_exp names e,
  some (seen, [stmt.return ce])

-- Translation of λow* decls

-- is it actually simpler to propagate seen across the translated decl?
def transl_decl : idents → lowstar.decl → option (idents × cstar.decl)
| seen (decl.function fn arg_ty body ret_ty) :=
  let id := fresh_ident seen in
  let arg_ty' := transl_typ arg_ty in
  let ret_ty' := transl_typ ret_ty in do
  (seen', ss) ← transl_to_stmt (set.insert id seen) (names_cons id names_empty) body,
  some (seen', decl.function ret_ty' fn (binder.mk id arg_ty') ss)
-- | seen (decl.global g τ v) :=
--   some (seen, decl.global g (transl_typ τ) v)

def transl_program : idents → lowstar.program → option (idents × cstar.program)
| seen [] := some (seen, [])
| seen (d :: ds) := do
  (seen', d') ← transl_decl seen d,
  (seen'', ds') ← transl_program seen' ds,
  some (seen'', d' :: ds')

-- Administrative lemmas

lemma transl_to_stmt_exp : ∀ {X} names seen (e : exp X) ce,
  transl_to_exp names e = some ce →
  transl_to_stmt seen names e = some (seen, [stmt.return ce])
:=
begin
  introv H, induction e; simp [transl_to_exp] at H;
  try { injection H with H' };
  try { rw -H', simp [transl_to_stmt, transl_to_exp], unfold has_bind.bind, simp [option_bind] }, -- ??
  opt_inv H,
  simp [transl_to_stmt, transl_to_exp], rw [H_1, H_3], unfold has_bind.bind, simp [option_bind]
end

end lowstar_to_cstar
