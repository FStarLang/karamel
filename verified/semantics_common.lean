import common

namespace semantics_common

open common

inductive label : Type
| read : location → label
| write : location → label
| branch_true : label
| branch_false : label

def memset_labels (block_id : nat) : nat -> nat -> list label
| start_offset 0 := []
| start_offset (nat.succ n) :=
  (label.write (block_id, start_offset, [])) ::
  memset_labels (nat.succ start_offset) n


-- FIXME: placeholder
def map (α : Type) (β : Type) :=
  α → option β

def map_add {α β : Type} (m : map α β) (x : α) (y: β) : map α β :=
  sorry

def map_empty {α β : Type} : map α β :=
  sorry

def map_singleton {α β : Type} : α → β → map α β :=
  sorry

end semantics_common
