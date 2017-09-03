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


