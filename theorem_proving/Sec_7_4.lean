namespace hide

  -- inductive nat : Type 
  -- | zero : nat 
  -- | succ : nat → nat

  -- #check @nat.rec_on

  -- namespace nat
  --   def add (m n : nat) : nat := 
  --   nat.rec_on n m (λ n add_m_n, succ add_m_n)

  --   #reduce add (succ zero) (succ (succ zero))

  --   instance : has_zero nat := has_zero.mk zero
  --   instance : has_add nat := has_add.mk add

  --   theorem add_zero (m : nat) : m + 0 = m := rfl
  --   theorem add_succ (m n : nat) : m + succ n = succ (m + n) := rfl

open nat
    theorem zero_add (n : nat) : 0 + n = n := 
    nat.rec_on n
      (show 0 + 0 = 0, from rfl)
      (assume n, 
        assume ih : 0 + n = n,
        show 0 + succ n = succ n, from 
          calc
            0 + succ n = succ (0 + n) : rfl
              ... = succ n : by rw ih)

end hide


--   end nat

-- end hide

-- namespace hide
-- open nat

