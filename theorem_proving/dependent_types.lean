-- Chapter 2. Dependent Type Theory

-- Section 2.1 Simple Type Theory

-- page 10 ------------------------------------------

/- declare some constants -/

constant m : nat  -- m is a natural number
constant n : nat


-- page 11 ------------------------------------------

constants b1 b2 : bool -- declare two constants at once (notice the plural)

/- check their types -/

#check m                          -- m : ℕ
#check n
#check n + 0
#check m * (n+0)
#check b1
#check b1 && b2                   -- b1 && b2 : bool
#check b1 || b2
#check tt                         -- tt : bool  (i.e., boolean true)
-- #check b1 + tt                 -- b1 + tt : bool (actually it's a type error)

constant f : nat → nat           -- type the arrow using `\to` or `\r`
constant f' : nat -> nat          -- alternative ASCII notation
constant f'' : ℕ → ℕ           -- `\nat` is alternative notation for `nat`
constant p : ℕ × ℕ              -- type the product using `\times`
constant q : prod nat nat         -- alternative notation
constant g : ℕ → ℕ → ℕ
constant g' : nat -> (nat -> nat) -- has the same type as g!
constant g'' : nat × nat -> nat   -- not the same type as g

constant F : (nat -> nat) -> nat  -- a "functional"

#check f
#check f n
#check g m
#check g m n
#check (m, n)
#check F
#check F f
#check p.1
#check p.1
#check (m, n).1
#check (p, n)
#check (p.1, n)
#check (n, f)
#check F (n, f).2   -- (output)  F((n, f).snd) : ℕ


/- Section 2.1 output of type-check results
                m : ℕ
                n : ℕ
                n + 0 : ℕ
                m * (n + 0) : ℕ
                b1 : bool
                b1 && b2 : bool
                b1 || b2 : bool
                tt : bool
                f : ℕ → ℕ
                f n : ℕ
                g m : ℕ → ℕ
                g m n : ℕ
                (m, n) : ℕ × ℕ
                F : (ℕ → ℕ) → ℕ
                F f : ℕ
                p.fst : ℕ
                p.fst : ℕ
                (m, n).fst : ℕ
                (p, n) : (ℕ × ℕ) × ℕ
                (p.fst, n) : ℕ × ℕ
                (n, f) : ℕ × (ℕ → ℕ)
                F ((n, f).snd) : ℕ
-/


-- Section 2.2 Types as Objects

-- page 12 

#check nat                     --  ℕ : Type
#check bool                    --  bool : Type
#check nat -> bool
#check nat -> (nat -> nat)  
#check list                    --  list : Type u_1 → Type u_1
#check prod                    --  prod : Type u_1 → Type u_2 → Type(max u_1 u_2)

-- page 13


constants α β : Type

constant H : Type → Type
constants G : Type → Type → Type

#check α
#check H α
#check H nat
#check G α
#check G α β
#check G α nat
#check list α



-- Types of types

#check Type                     -- Type : Type 1
#check Type 0                   -- Type : Type 1
#check Type 1                   -- Type 1 : Type 2
#check Type 2                   -- Type 2 : Type 3
#check Type 3                   -- etc.
#check Type 4


-- page 14

#check Prop                     -- Prop : Type


-- Polymorphism

/- To define polymorphic constants and variables, Lean allows us to declare 
   universe variables explicitly:                             -/
universe u
constant γ : Type u
#check γ

/- the ability to treat type constructors as instances of 
   ordinary mathematical functions is a powerful feature of 
   dependent type theory.         -/

/- Section 2.2 output of type-check results
                ℕ : Type
                bool : Type
                ℕ → bool : Type
                ℕ → ℕ → ℕ : Type
                list : Type u_1 → Type u_1
                prod : Type u_1 → Type u_2 → Type (max u_1 u_2)
                α : Type
                H α : Type
                H ℕ : Type
                G α : Type → Type
                G α β : Type
                G α ℕ : Type
                list α : Type
                Type : Type 1
                Type : Type 1
                Type 1 : Type 2
                Type 2 : Type 3
                Type 3 : Type 4
                Type 4 : Type 5
                Prop : Type
                γ : Type u_1
-/
 


-- Section 2.3. Function Abstraction and Evaluation

-- page 15 (lambda abstraction)
namespace page15
  #check fun x : nat, x + 5
  #check λ x : ℕ, x + 5
  constants α β : Type
  constants a1 a2 : α
  constants b1 b2 : β
  constant f : α → α
  constant g : α → β
  constant h : α → β → α
  constant p : α → α → bool
  #check fun x : α, f x
  #check λ x : α, f x
  #check λ x : α, f (f x)
end page15


namespace page16
  constants α β γ : Type
  constant f : α → β
  constant g : β → γ
  constant b : β
  #check λ x : α, x
  #check λ x : α, b
  #check λ x : α, g (f x)
  #check λ x, g (f x)
end page16

/- Section 2.3 output of type-check results
                λ (x : ℕ), x + 5 : ℕ → ℕ
                λ (x : ℕ), x + 5 : ℕ → ℕ
                λ (x : α), f x : α → α
                λ (x : α), f x : α → α
                λ (x : α), f (f x) : α → α
                λ (x : α), x : α → α
                λ (x : α), b : α → β
                λ (x : α), g (f x) : α → γ
                λ (x : α), g (f x) : α → γ
-/

