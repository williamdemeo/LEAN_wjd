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

example: even 10 := ⟨5, rfl⟩

end


