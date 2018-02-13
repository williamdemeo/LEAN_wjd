-- Chapter 1. Overview

#check "hello, world!"

-- page 6
namespace hide  

inductive nat: Type
| zero: nat
| succ: nat → nat

def add: nat → nat → nat
| m nat.zero := m
| m (nat.succ n) := nat.succ (add m n)

#eval add nat.zero (nat.succ (nat.succ nat.zero))

end hide

def double (n: ℕ) : ℕ := n + n

#check double
#print double
#eval double 2


-- page 7
section 
  variables (G : Type) [group G]
  variables g₁ g₂ : G

  #check g₂⁻¹ * g₁ * g₂
  #check g₁⁻¹ * g₁
end


-- page 8
/- An important feature of dependent type theory is that every expression
  has a computational interpretation, which is to say, there are rules
  that specify how they can be /reduced/ to a normal form. 
  Moreover, expressions in a computationally pure fragment of the language
  evaluate to /values/ in the way you would expect. 
  For example, assuming the definition does not depend on nonconstructive 
  components in an essential way, every closed term of type =ℕ= evaluates 
  to a numeral. Lean's kernel can carry out this evaluation: -/

#eval (27 + 9) * 33

/- As part of the kernel, the results of this evaluation can be highly trusted. 
  The evaluator is not very efficient, however, and is not intended to be used 
  for substantial computational tasks. For that purpose, Lean also generates 
  bytecode for every definition of a computable object, and can evaluate it on 
  demand. To process the bytecode quickly, it uses an efficient /virtual machine/, 
  similar to the ones used to interpret OCaml and Python. -/

--def double (n : ℕ) : ℕ := n + n

#eval (27 + 9) * 33
#eval (2227 + 9999) * 33
#eval double 9999
#eval [(1, 2), (3, 4), (5, 6)] ++ [(7, 8), (9, 10)]

/- Relying on results from the bytecode evaluator requires a higher level
  of trust than relying on the kernel. For example, for efficiency, the
  bytecode evaluator uses the GNU multiple precision library to carry out
  numerical computations involving the natural numbers and integers, so
  the correctness of those computations are no longer underwritten by
  the axiomatic foundation. -/

/- This points to a second intended use of Lean, namely, as a
  /programming language/. Because dependent type theory is so
  expressive, we can make use of all the usual methods and techniques of
  functional programming, including higher types, type classes, records,
  monads, and other abstractions. 

  For example, we can write a generic sort procedure that sorts elements 
  of a list according to a specified binary relation =r= on an arbitrary 
  type =α=, assuming only that we can determine computationally when =r= holds. -/

section sort
  universe u
  parameters {α : Type u} (r : α → α → Prop) [decidable_rel r]
  local infix `≼` : 50 := r

  def ordered_insert (a : α) : list α → list α
  | []       := [a]
  | (b :: l) := if a ≼ b then a :: (b :: l) else b :: ordered_insert l

  def insertion_sort : list α → list α
  | []       := []
  | (b :: l) := ordered_insert b (insertion_sort l)


-- We can run the procedure above on a list of natural numbers, using the usual ordering:

#eval insertion_sort (λ m n : ℕ, m ≤ n) [5, 27, 221, 95, 17, 43, 7, 2, 98, 567, 23, 12]

end sort

-- Substantial programs can be written in Lean and run by the bytecode interpreter. 

-- page 9
section 
def even (n : ℕ) : Prop := ∃ m, n = 2 * m
#check even 10
#check even 11
#check ∀ n, even n ∨ even (n + 1)
#check ∀ n m, even n → even m → even (n + m)


-- Here is how we prove 10 is even.
example: even 10 := ⟨5, rfl⟩

/- To prove an existential statement, it is enough to present a witness to the
   existential quantifier and then show that the claim is true of that witness. 
   The Unicode angle brackets just package this data together; enter them in emacs
   with \< and \>, or use the ASCII equivalents, (| and |). -/

-- Here is a proof that the sum of two evens is even.
theorem even_add : ∀ m n, even m → even n → even (m + n) :=
take m n
assume ⟨k, (Hk : m = 2 * k)⟩
assume ⟨l, (Hl : n = 2 * l)⟩
have m + n = 2 * (k + l),
  by simp [Hk, Hl, mul_add]
show even (m + n), 
  from ⟨ _ , this⟩


end

