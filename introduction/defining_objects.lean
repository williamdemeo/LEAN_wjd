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
#check (a₁, a₂)
#check (n, b)
#check p.1
#check p.2
#check q.1
#check q.2

#reduce (n, b).1
#eval (2, 3).1
#reduce (2, 3).2
#eval (2, 3).2

#check (n, a₁, b)   -- associates to the right: (n, (a₁, b))
#reduce (n, a₁, b).2
#reduce (n, a₁, b).2.2
