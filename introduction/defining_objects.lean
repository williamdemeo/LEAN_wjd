-- Chapter 2. Defining Objects in Lean

-- page 15
#check nat
#print nat

#check int
#print int

#check list
#print list

#check bool
#print bool

#check 3 + 6 * 9
#eval 3 + 6 * 9

-- page 17
#check (≤)

variables α β : Type
variables (a₁ a₂ : α) (b : β) (n : ℕ)
variables (p: α × β) (q : α × ℕ)

#check α × β
