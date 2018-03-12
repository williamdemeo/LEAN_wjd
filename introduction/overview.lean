-- File: overview.lean
-- Author: williamdemeo@gmail.com
-- Date: 1 Feb 2018
/- Desc: A collection of things I tried while working throught the introduction_to_lean tutorial. -/

namespace hide

inductive nat: Type
| zero : nat
| succ : nat → nat

def add : nat → nat → nat
| m nat.zero := m
| m (nat.succ n) := nat.succ (add m n)

end hide


-- theorem add_assoc : ∀ m n l : ℕ, add (add m n) l = add m (add n l) :=
-- begin
--   induction n with n ih,

-- end
