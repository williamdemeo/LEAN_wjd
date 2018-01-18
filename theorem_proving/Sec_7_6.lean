universe u
def tuple (α : Type u) (n : ℕ) := 
  { l : list α // list.length l = n }

#check tuple

variables {α : Type u} {n : ℕ}

def f {n : ℕ} (t : tuple α n) : ℕ :=
begin 
  cases n, exact 3, exact 7
end

#check f

def my_tuple : tuple ℕ 3 := ⟨[0, 1, 2], rfl⟩

example : f my_tuple = 7 := rfl
  -- Again, we prove that f n is constantly 7, except when n = 0.
  -- example  (n : ℕ) (t : tuple ℕ n) (h : n ≠ 0) : ftuple t = 7 := 
  -- begin
  --   cases n,
  --   { apply (absurd rfl h) },  -- goal: 0 ≠ 0 ⊢ f 0 = 7
  --   reflexivity                -- goal: (succ a ≠ 0) ⊢ f (succ a) = 7
  -- end
