-- Chapter 2. Dependent Type Theory

#print "------------------------------------------------"
#print "Section 2.1 Simple Type Theory"

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


#print "------------------------------------------------"
#print "Section 2.2 Types as Objects"


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
 


#print "------------------------------------------------"
#print "Section 2.3. Function Abstraction and Evaluation"

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

-- We can abstract over any of the constants in the previous definitions.

  #check λ b : β, λ x : α, x    -- β → α → α
  #check λ (b : β) (x : α), x   -- β → α → α   (same as previous line)
  #check λ (g : α → β) (f : β → γ) (x : α), f (g x)

-- We can even abstract over the type.

#check λ (α β : Type) (b : β) (x : α), x
#check λ (α β γ : Type) (g: α → β) (f: β → γ) (x: α), f (g x)  
/- the last expression has "pi-type" 
   Π (α β γ : Type) (α → β) → (β → γ) → α → γ
   which is the type that, for all types α, β, γ, takes maps of types
   α → β and β → γ, and returns their composition (a map of type α → γ)
-/
end page16

namespace page17
  constants α β γ : Type
  constant f : α → β
  constant g : β → γ
  constant h : α → α
  constants (a : α) (b : β)

  #check (λ x : α, x) a                                        -- α
  #check (λ x : α, b) a                                        -- β
  #check (λ x : α, b) (h a)                                    -- β
  #check (λ x : α, g (f x)) (h (h a))                          -- γ

  #check (λ (v : β → γ) (u : α → β) x, v (u x)) g f a        -- γ

  #check (λ (Q R S : Type) (v : R → S) (u: Q → R) (x : Q), 
         v (u x)) α β γ g f a                                  -- γ

-- `#reduce` tells Lean to evaluate an expression by reducing to normal form.
  #reduce (λ x : α, x) a                                        -- a
  #reduce (λ x : α, b) a                                        -- b
  #reduce (λ x : α, b) (h a)                                    -- b
  #reduce (λ x : α, g (f x)) (h (h a))                          -- g (f (h (h a)))

  #reduce (λ (v : β → γ) (u : α → β) x, v (u x)) g f a        -- g (f a)

  #reduce (λ (Q R S : Type) (v : R → S) (u: Q → R) (x : Q), 
         v (u x)) α β γ g f a                                   -- g (f a)

-- `#reduce` carries out more than just β reductions.
  constants m n : nat
  constant s : bool

  #print "reducing pairs"
  #reduce (m, n).1                       -- m
  #reduce (m, n).2                       -- n

  #print "reducing boolean expressions"
  #reduce tt && ff                       -- ff
  #reduce s && ff                        -- bool.rec ff ff s
  #reduce ff && s                        -- ff

  #print "reducing arithmetic expressions"
  #reduce n + 0
  #reduce n + 2
  #reduce 2 + 3

end page17


/- This is an important feature of dependent type theory:
   every term has a computational behavior, and supports a notion of reduction, 
   or normalization. In principle, two terms that reduce to the same value are 
   called definitionally equal. 

-/

/- It is the computational behavior illustrated above that makes it possible to 
   use Lean as a programming language as well as a proof assistant. 

   Lean extracts bytecode from terms in a computationally pure fragment of the 
   logical framework, and can evaluate them quite efficiently.
-/

  #eval 12345 * 54321

/- In contrast, the #reduce command relies on Lean's trusted kernel, the part 
   of Lean that is responsible for checking and verifying the correctness of 
   expressions and proofs. As such, the `#reduce` command is more trustworthy, 
   but far less efficient. 
-/



/- Section 2.3 output
                λ (x : ℕ), x + 5 : ℕ → ℕ
                λ (x : ℕ), x + 5 : ℕ → ℕ
                λ (x : α), f x : α → α
                λ (x : α), f x : α → α
                λ (x : α), f (f x) : α → α
                λ (x : α), x : α → α
                λ (x : α), b : α → β
                λ (x : α), g (f x) : α → γ
                λ (x : α), g (f x) : α → γ
                λ (b : β) (x : α), x : β → α → α
                λ (b : β) (x : α), x : β → α → α
                λ (g : α → β) (f : β → γ) (x : α), f (g x) : 
                   (α → β) → (β → γ) → α → γ
                λ (α β : Type) (b : β) (x : α), x : Π (α β : Type), β → α → α
                λ (α β γ : Type) (g : α → β) (f : β → γ) (x : α), f (g x) :
                    Π (α β γ : Type), (α → β) → (β → γ) → α → γ
                (λ (x : α), x) a : α
                (λ (x : α), b) a : β
                (λ (x : α), b) (h a) : β
                (λ (x : α), g (f x)) (h (h a)) : γ
                (λ (v : β → γ) (u : α → β) (x : α), v (u x)) g f a : γ
                (λ (Q R S : Type) (v : R → S) (u : Q → R) (x : Q), v (u x)) 
                   α β γ g f a : γ
                a
                b
                b
                g (f (h (h a)))
                g (f a)
                g (f a)
                reducing pairs
                m
                n
                reducing boolean expressions
                ff
                bool.rec ff ff s
                ff
                reducing arithmetic expressions
                n
                nat.succ (nat.succ n)
                5
                670592745
-/

#print "------------------------------------------------"
#print "Section 2.4. Introducing Definitions"

/- Declaring constants is a good way to postulate new objects to experiment with.
   But most of the time we want to define objects in Lean and prove things about them. 
   The definition command provides one important way of defining new objects.
-/

namespace page18
  definition foo : (ℕ → ℕ) → ℕ := λ f, f 0
  #check foo
  #print foo
  #reduce foo (λ x : ℕ, x * 2)
end page18

/- We can use a shorthand `def` and an alternative format that puts the 
   abstracted variables before the colon and odmits the lambda. -/

namespace page19
  def double (x : ℕ) : ℕ := x + x
  #check double                                        -- ℕ → ℕ
  #print double
  #reduce double 3                                     -- 6

  def square (x : ℕ) := x*x
  #check square                                        -- ℕ → ℕ
  #print square
  #reduce square 3                                     -- 9

  def do_twice (f : ℕ → ℕ) (x : ℕ) := f (f x)
  #reduce do_twice double 2                            -- 8

  -- we could have defined the last three terms thus:
  def double_alt : ℕ → ℕ := λ x, x + x
  def square_alt : ℕ → ℕ := λ x, x*x
  def do_twice_alt : (ℕ → ℕ) → ℕ → ℕ := λ (f: ℕ → ℕ) (x: ℕ), f (f x)
  #check do_twice_alt
  #print do_twice_alt
  #reduce do_twice_alt double 2

  /- As an exercise, we encourage you to use do_twice and double to define 
     functions that quadruple their input, and multiply the input by 8.   -/  
  def quadruple : ℕ → ℕ := do_twice double
  #check quadruple
  #reduce quadruple 2

  def mult_by_eight := λ x, (do_twice double 2) * x
  #check mult_by_eight
  #reduce mult_by_eight 4

  /- As a further exercise, we encourage you to try defining a function 
                Do_Twice : ((N → N) → (N → N)) → (N → N) → (N → N) 
     which applies its argument twice, so that `Do_Twice do_twice` is a 
     function that iterates its input four times.  -/   
  def Do_Twice : ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → (ℕ → ℕ) :=
                 λ (f: (ℕ → ℕ) → (ℕ → ℕ)) (g: ℕ → ℕ), f (f g)

  -- Finally, evaluate `Do_Twice do_twice double 2`.
  #reduce Do_Twice do_twice double 2                    -- 32

  /- As another exercise, we encourage you to complete the following
     definitions, which "curry" and "uncurry" a function. -/
  def curry (α β γ : Type) (f : α × β → γ) : α → β → γ := 
         λ (x : α) (y : β), f (x, y)

  def uncurry (α β γ : Type) (f : α → β → γ) : α × β → γ :=
         λ (p : α × β), f p.1 p.2

end page19

/- Section 2.4. output:
                foo : (ℕ → ℕ) → ℕ
                def page18.foo : (ℕ → ℕ) → ℕ :=
                λ (f : ℕ → ℕ), f 0
                0
                double : ℕ → ℕ
                def page19.double : ℕ → ℕ :=
                λ (x : ℕ), x + x
                6
                square : ℕ → ℕ
                def page19.square : ℕ → ℕ :=
                λ (x : ℕ), x * x
                9
                8
                do_twice_alt : (ℕ → ℕ) → ℕ → ℕ
                def page19.do_twice_alt : (ℕ → ℕ) → ℕ → ℕ :=
                λ (f : ℕ → ℕ) (x : ℕ), f (f x)
                8
                quadruple : ℕ → ℕ
                8
                mult_by_eight : ℕ → ℕ
                32
                32
-/


#print "------------------------------------------------"
#print "Section 2.5. Local Definitions"

-- Lean allows you to introduce "local" definitions using the let construct.

/- The expression let `a := t1 in t2` is definitionally equal to the result of 
   replacing every occurrence of `a` in `t2` by `t1`. -/
namespace page20
  #check let y := 2 + 2 in y * y                     -- ℕ
  #reduce let y := 2 + 2 in y * y                    -- 16
  def t (x : ℕ) : ℕ := let y := x + x in y * y
  #reduce t 2                                        -- 16
end page20


#print "------------------------------------------------"
#print "Section 2.6. Variables and Sections"

-- some organizational features of Lean (not part of axiomatic framework per se)

/- Recall, the `constant` command allows us to declare new objects, which
   then become part of the global context. This can be somewhat dangerous since 
   declaring a new constant is tantamount to declaring an axiomatic extension of 
   our foundational system, and may result in inconsistency.

   This can be avoided, using implicit or explicit lambda abstraction
   in our definitions to declare such objects "locally".
-/
namespace page21

  def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ := g (f x)

  def do_twice (α : Type) (h : α → α) (x : α) : α := h (h x)

  /- Repeating declarations in this way can be tedious, however. Lean provides us with
     the `variable` and `variables` commands to make such declarations look global:
  -/
  variables (α β γ : Type)
  def compose_alt (g : β → γ) (f : α → β) (x : α) : γ := g (f x)

end page21
/- The variable and variables commands look like the constant and constants commands, 
   but there is an important difference. Rather than creating permanent entities, 
   the `variables` command simply instructs Lean to insert the declared variables 
   as bound variables in definitions that refer to them. -/

#print "------------------------------------------------"
#print "Section 2.7 Namespaces"
/- Namespaces and sections serve different purposes: namespaces organize data and sec-
tions declare variables for insertion in theorems. -/

#print "------------------------------------------------"
#print "Section 2.8 Dependent Types"

#print "------------------------------------------------"
#print "Section 2.9 Implicit Arguments"

#print "------------------------------------------------"
#print "Section 2.10 Exercises"
