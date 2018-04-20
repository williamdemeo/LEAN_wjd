namespace Sec_4_6

-- 4.1. Prove these equivalences:
     -- variables (α : Type) (p q : α → Prop)
     -- example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := sorry
     -- example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry
     -- example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry
     -- You should also try to understand why the reverse implication is not 
     -- derivable in the last example.
  namespace exercise_4_1
    variables (α : Type) (p q : α → Prop)
    example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := iff.intro
      (assume h : ∀ x, p x ∧ q x,
        and.intro 
        (assume w,
          show p w, from (h w).left)
        (assume w,
          show q w, from (h w).right))
      (assume h : (∀ x, p x) ∧ (∀ x, q x),
        assume w,
        ⟨(h.left w), (h.right w)⟩)
    example : (∀ x, (p x → q x)) → (∀ x, p x) → (∀ x, q x) := 
      assume h₁ : ∀ x, (p x → q x),
      assume h₂ : (∀ x, p x),
      assume w,
      have h₃ : p w, from h₂ w,
      show q w, from h₁ w h₃
    example : (∀ x, p x) ∨ (∀ x, q x) → (∀ x, p x ∨ q x) := 
      assume h: (∀ x, p x) ∨ (∀ x, q x),
      assume w,
        or.elim h
          (assume hl : ∀ x, p x,
            show p w ∨ q w, from or.intro_left _ (hl w))
          (assume hr : ∀ x, q x,
            show p w ∨ q w, from or.intro_right _ (hr w))
  end exercise_4_1

---

-- 4.2. It is often possible to bring a component of a formula outside a universal quantifier, 
--      when it does not depend on the quantified variable. Try proving these 
--      (one direction of the second of these requires classical logic):
       -- variables (α : Type) (p q : α → Prop)
       -- variable r : Prop
       -- example : α → ((∀ x : α, r) ↔ r) := sorry
       -- example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
       -- example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry
    namespace exercise_4_2
       variables (α : Type) (p q : α → Prop)
       variable r : Prop
       example : α → ((∀ x : α, r) ↔ r) := assume h0 : α, 
         iff.intro
         (show (∀ x : α, r) → r, from assume h1 : (∀ x: α, r), h1 h0)
         (show r → ∀ x : α, r, from assume (h2: r) (w: α), show r, from h2)

       open classical
       example : (∀ (x:α), p x ∨ r) ↔ (∀ (x:α), p x) ∨ r := iff.intro
         -- the forward direction requires classical logic
         (show (∀ (x:α), p x ∨ r) → (∀ (x:α), p x) ∨ r, from 
           assume h1: (∀ (x:α), p x ∨ r),
           or.elim (em r)
             (assume hr: r, or.inr hr)
             (assume hnr: ¬r, or.inl 
             (assume x:α, or.elim (h1 x) 
               (assume hpx: p x, hpx)
               (assume hr : r, false.elim (hnr hr)))))
         (show (∀ x, p x) ∨ r → (∀ x, p x ∨ r), from 
           assume h: (∀ x, p x) ∨ r, 
           or.elim h
             (assume hl : ∀ x, p x, assume w: α, or.inl (hl w))
             (assume hr : r, assume w: α, or.inr hr))


       example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := iff.intro
         (assume h1: (∀ x, r → p x), show (r → ∀ x, p x), from 
           assume (hr: r) (w:α), h1 w hr)
         (assume h2: (r → ∀ x, p x), show (∀ x, r → p x), from 
           assume w:α, show r → p w, from (assume hr: r, h2 hr w))


    end exercise_4_2

---

-- 4.3 Consider the "barber paradox," that is, the claim that in a certain town there 
--     is a (male) barber that shaves all and only the men who do not shave themselves. 
--     Prove that this is a contradiction:
       -- variables (man : Type) (barber : man) 
       -- variable  (shaves : man → man → Prop)
       -- example (h : ∀ x : man, shaves barber x ↔ ¬ shaves x x) : false :=
   namespace exercise_4_3
     variables (man : Type) (barber : man) 
     variable  (shaves : man → man → Prop)

     open classical  -- It would seem we will need lem.
     -- First try
     example (h : ∀ x : man, shaves barber x ↔ ¬ shaves x x) : false :=
       let p := (shaves barber barber) in
       or.elim (em p)
       (assume (hp: p), iff.elim_left (h barber) hp hp)
       (assume hnp: ¬ p, hnp (iff.elim_right (h barber) hnp))

     -- We can clean this up with a lemma (that may be useful elsewhere).
     lemma p_iff_not_p__false (p : Prop) (h: p ↔ ¬ p) : false := or.elim (em p)
       (assume hp: p, iff.elim_left h hp hp)
       (assume hnp: ¬ p, hnp (iff.elim_right h hnp))
       
     -- Second try
     example (h : ∀ x : man, shaves barber x ↔ ¬ shaves x x) : false :=
       let p := (shaves barber barber) in p_iff_not_p__false p (h barber)
     -- Third try
     example (h : ∀ x : man, shaves barber x ↔ ¬ shaves x x) : false :=
       p_iff_not_p__false (shaves barber barber) (h barber)
   end exercise_4_3


-- 4.4 Below, we have put definitions of ``divides`` and ``even`` in a special namespace 
--     to avoid conflicts with definitions in the library. The ``instance`` declaration 
--     make it possible to use the notation ``m | n`` for ``divides m n``. Don't worry 
--     about how it works; you will learn about that later.
       namespace exercise_4_4
       def divides (m n : ℕ) : Prop := ∃ k, m * k = n
       instance : has_dvd nat := ⟨divides⟩
       def even (n : ℕ) : Prop := 2 ∣ n
       section
         variables m n : ℕ
         #check m ∣ n
         #check m^n
         #check even (m^n +3)
       end
       end exercise_4_4

--     Remember that, without any parameters, an expression of type ``Prop`` is just an assertion. 
--     Fill in the definitions of ``prime`` and ``Fermat_prime`` below, and construct the given 
--     assertion.  For example, you can say that there are infinitely many primes by asserting 
--     that for every natural number ``n``, there is a prime number greater than ``n``. 
--     Goldbach's weak conjecture states that every odd number greater than 5 is the sum of 
--     three primes. Look up the definition of a Fermat prime or any of the other statements, 
--     if necessary.
       -- namespace hide
       --   def divides (m n : ℕ) : Prop := ∃ k, m * k = n
       --   instance : has_dvd nat := ⟨divides⟩
       --   def even (n : ℕ) : Prop := 2 ∣ n
       --   def prime (n : ℕ) : Prop := sorry
       --   def infinitely_many_primes : Prop := sorry
       --   def Fermat_prime (n : ℕ) : Prop := sorry
       --   def infinitely_many_Fermat_primes : Prop := sorry
       --   def goldbach_conjecture : Prop := sorry
       --   def Goldbach's_weak_conjecture : Prop := sorry
       --   def Fermat's_last_theorem : Prop := sorry
       -- end hide
       namespace exercise_4_4_solution
         def divides (m n : ℕ) : Prop := ∃ k, m * k = n
         instance : has_dvd nat := ⟨divides⟩
         def even (n : ℕ) : Prop := 2 ∣ n
         def prime (n : ℕ) : Prop := ∀ (m:ℕ), (divides m n) → (m = 1 ∨ m = n)
         def infinitely_many_primes : Prop := ∀ n : ℕ, ∃ p : ℕ, prime p ∧ p > n
         def Fermat_prime (n : ℕ) : Prop := ∃ k : ℕ, 2^(2^k) = n
         def infinitely_many_Fermat_primes : Prop := ∀ n : ℕ, ∃ p : ℕ, Fermat_prime p ∧ p > n
         def goldbach_conjecture : Prop := 
           ∀ n : ℕ, even n ∧ (n>2) → ∃ j k, prime j ∧ prime k ∧ j+k = n
         def Goldbach's_weak_conjecture : Prop := 
           ∀ n : ℕ, ¬ even n ∧ (n>5) → ∃ j k l, prime j ∧ prime k ∧ prime l ∧ j+k+l = n
         def Fermat's_last_theorem : Prop := ∀ (n:ℕ) (a b c :ℕ), n > 2 → ¬ (a^n + b^n = c^n)
       end exercise_4_4_solution

---

-- 4.5 Prove as many of the identities listed in :numref:`the_existential_quantifier` as you can.
       -- variables (α : Type) (p q : α → Prop)
       -- variable a : α
       -- variable r : Prop
       -- example : (∃ x : α, r) → r := sorry
       -- example : r → (∃ x : α, r) := sorry
       -- example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := sorry
       -- example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry
       -- example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
       -- example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
       -- example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
       -- example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry
       -- example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
       -- example : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
       -- example : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
     namespace exercise_4_5
       variables (α : Type) (p q : α → Prop)
       variable a : α
       variable r : Prop

       example : (∃ x : α, r) → r := 
         assume h: (∃ x : α, r), exists.elim h (assume w r, r)

       example : r → (∃ x : α, r) := assume hr: r, exists.intro a hr

       example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := iff.intro
         (assume h1: ∃ x, p x ∧ r, show (∃ x, p x) ∧ r, from 
           exists.elim h1
           (assume w, assume h: p w ∧ r, ⟨⟨w, h.left⟩, h.right⟩)
         )
         (assume h2 : (∃ x, p x) ∧ r, show (∃ x, p x ∧ r), from 
           exists.elim h2.left 
           (assume w, assume hw : p w, ⟨w, hw, h2.right⟩)
         )

       example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := iff.intro
         (assume h : (∃ x, p x ∨ q x), show (∃ x, p x) ∨ (∃ x, q x), from 
           exists.elim h
           (assume w, assume hw : p w ∨ q w, 
             or.elim hw
               (assume hl : p w, or.inl (exists.intro w hl))
               (assume hr : q w, or.inr (exists.intro w hr))
           )
         )
         (assume h : (∃ x, p x) ∨ (∃ x, q x), show (∃ x, p x ∨ q x), from 
           or.elim h
             (assume hl : (∃ x, p x), 
               exists.elim hl
                 (assume w, assume hpw : p w, exists.intro w (or.inl hpw)))
             (assume hr : (∃ x, q x),
               exists.elim hr
                 (assume w, assume hqw : q w, exists.intro w (or.inr hqw)))
         )

       example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := iff.intro
         (assume h : (∀ x, p x), show ¬ (∃ x, ¬ p x), from 
           assume hn : (∃ x, ¬ p x), show false, from -- LEFT OFF HERE
         )
         (assume h : ¬ (∃ x, ¬ p x), show (∀ x, p x), from 

         )
       -- example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
       -- example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
       -- example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry
       -- example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
       -- example : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
       -- example : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
   end exercise_4_5
---

-- 4.6 Give a calculational proof of the theorem ``log_mul`` below.
       -- variables (real : Type) [ordered_ring real]
       -- variables (log exp : real → real)
       -- variable  log_exp_eq : ∀ x, log (exp x) = x
       -- variable  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
       -- variable  exp_pos    : ∀ x, exp x > 0
       -- variable  exp_add    : ∀ x y, exp (x + y) = exp x * exp y
       -- -- this ensures the assumptions are available in tactic proofs
       -- include log_exp_eq exp_log_eq exp_pos exp_add
       -- example (x y z : real) : 
       --   exp (x + y + z) = exp x * exp y * exp z := by rw [exp_add, exp_add]
       -- example (y : real) (h : y > 0)  : exp (log y) = y := exp_log_eq h
       -- theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) : 
       --   log (x * y) = log x + log y := sorry

       variables (real : Type) [ordered_ring real]
       variables (log exp : real → real)
       variable  log_exp_eq : ∀ x, log (exp x) = x
       variable  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
       variable  exp_pos    : ∀ x, exp x > 0
       variable  exp_add    : ∀ x y, exp (x + y) = exp x * exp y
       -- this ensures the assumptions are available in tactic proofs
       include log_exp_eq exp_log_eq exp_pos exp_add
       example (x y z : real) : 
         exp (x + y + z) = exp x * exp y * exp z := by rw [exp_add, exp_add]
       example (y : real) (h : y > 0)  : exp (log y) = y := exp_log_eq h

       theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) : 
         log (x * y) = log x + log y :=
         calc log (x * y) = log ((exp (log x)) * y) : by rw exp_log_eq hx
                      ... = log ((exp (log x)) * (exp (log y))) : by rw exp_log_eq hy
                      ... = log (exp (log x + log y)) : by rw exp_add
                      ... = log x + log y : by rw log_exp_eq

-- 4.7 Prove the theorem below, using only the ring properties of ``ℤ`` enumerated in the Section 4.2 Equality and the theorem ``sub_self``.
       -- #check sub_self
       -- example (x : ℤ) : x * 0 = 0 := sorry

       #check sub_self
       example (x : ℤ) : x * 0 = 0 := 
         calc x * 0 = x * (0 - 0) : by rw sub_self
               ... = x * 0 - x * 0 : mul_sub x 0 0
               ... = 0 : by rw sub_self


    
end Sec_4_6
