import common

namespace cstar

open common

inductive typ : Type
| int : typ
| pointer : typ → typ
| void : typ
-- | array : typ → typ -- ?
| function : typ → list typ → typ
-- | struct : list (common.field × typ) → typ

structure binder : Type :=
  mk :: (name : ident) (typ : typ)

inductive exp : Type
| int : nat → exp
| unit : exp
| var : ident → exp
| ptr_add : exp → exp → exp
| struct : list (common.field × exp) → exp
| field : exp → common.field → exp
| field_addr : exp → common.field → exp
| loc : location → exp

def exp_of_value : value → cstar.exp
| (value.int n) := exp.int n
| value.unit := exp.unit
--| (value.struct s) := exp.struct (exp_of_value_fields s)
| (value.loc l) := exp.loc l

instance : has_coe value cstar.exp := ⟨exp_of_value⟩

inductive stmt : Type
| decl : binder → exp → stmt
| decl_buf : binder → nat → stmt
| write_buf : exp → nat → exp → stmt
| call : ident → glob → exp → stmt
| read : ident → exp → stmt
| write : exp → exp → stmt
| if_then_else : exp → list stmt → list stmt → stmt
| block : list stmt → stmt
| ignore : exp → stmt
| return : exp → stmt

inductive decl : Type
| function : typ → glob → binder → list stmt → decl
-- | global : glob → typ → value → decl

def program : Type :=
  list decl

end cstar
