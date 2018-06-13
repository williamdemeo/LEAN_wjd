-- 8. Induction and Recursion


#print "==========================================="
#print "Section 8.1. Pattern Matching"
#print " "

namespace Sec_8_1
    open nat
    def sub0 : ℕ → ℕ
    | zero := zero
    | (succ x) := x

    #reduce sub0 zero               -- 0
    #reduce sub0 (succ zero)        -- 0
    #reduce sub0 (succ (succ zero)) -- 1

    def is_zero : ℕ → Prop
    | zero := true
    | (succ x) := false

    #reduce is_zero zero                -- true
    #reduce is_zero (sub0 (succ zero))  -- true
    #reduce is_zero (succ zero)         -- false

    -- The equations used to define these function hold definitionally:

    example : sub0 0 = 0 := rfl
    example (n: ℕ) : sub0 (succ n) = n := rfl
    example : is_zero zero = true := rfl
    example : is_zero (sub0 (succ zero))  = true :=rfl
    example : is_zero (succ zero) = false := rfl
    example (n: ℕ) : ¬ is_zero (n + 3) := not_false -- N.B. you can't use 
                                               -- `¬ false` here, although
    #check not_false                         -- <- this line gives `¬false`

    -- Pattern matching works with any inductive type, such as product and option.
    universes u v
    variables {α : Type u} {β: Type v} 

    def swap_pair : α × β → β × α | (a, b) := (b, a)
    #reduce swap_pair (2, 3)   -- result (3,2)

    def sum_pair : ℕ × ℕ → ℕ | (m, n) := m + n
    #reduce sum_pair (2,3)   -- result: 5

    def bar : option ℕ → ℕ × bool
    | (some n) := (n,tt)
    | none := (0,ff)
    #reduce bar (some 3)
    #reduce bar none

    -- Here we use pattern matching to define a function, and do a proof by cases.
    def bnot : bool → bool
    | tt := ff
    | ff := tt

    theorem bnot_involutive : ∀ (b:bool), bnot (bnot b) = b 
    | tt := rfl   -- proof that bnot (bnot tt) = tt
    | ff := rfl   -- proof that bnot (bnot ff) = ff

    -- Pattern matching can also be used to destruct inductively defined props.

    example (p q : Prop) : p ∧ q → q ∧ p
    | (and.intro hp hq) := and.intro hq hp

    example (p q: Prop) : p ∨ q → q ∨ p
    | (or.inl hp) := or.inr hp
    | (or.inr hq) := or.inl hq

    def sub1 : ℕ → ℕ 
    | zero := zero
    | (succ zero) := zero
    | (succ (succ n)) := n

    -- The defining equations hold "definitionally."
    example : sub1 0 = 0 := rfl
    example : sub1 1 = 0 := rfl
    example : sub1 2 = 0 := rfl
    example : sub1 3 = 1 := rfl
    example : sub1 4 = 2 := rfl



    def sub2 : ℕ → ℕ 
    | 0 := 0
    | 1 := 0
    | (a+2) := a

    -- See how Lean compiles the function to recursors:
    #print sub2._main
    #print id_rhs

    -- The defining equations hold "definitionally."
    example : sub2 0 = 0 := rfl
    example : sub2 1 = 0 := rfl
    example : sub2 2 = 0 := rfl
    example : sub2 3 = 1 := rfl
    example (a: ℕ): sub2 (a+2) = a := rfl

    def sub3 : ℕ → ℕ 
    | zero := zero
    | (succ zero) := zero
    | (succ (succ n)) := succ n
    -- The defining equations hold "definitionally."
    example : sub3 0 = 0 := rfl
    example : sub3 1 = 0 := rfl
    example : sub3 2 = 1 := rfl
    example : sub3 3 = 2 := rfl

    def sub4 : ℕ → ℕ 
    | 0 := 0
    | 1 := 0
    | (n+2) := n+1

    example : sub4 0 = 0 := rfl
    example : sub4 1 = 0 := rfl
    example : sub4 2 = 1 := rfl
    example : sub4 3 = 2 := rfl
    example : sub4 4 = 3 := rfl
    example (a: ℕ): sub4 (a+2) = a+1 := rfl -- holds definitionally

    -- example (a: ℕ): sub4 (a+1) = a   -- does not hold definitionally
    -- We could have defined `sub4` like this:
    def sub5 : ℕ → ℕ 
    | 0 := 0
    | n := n-1

    -- `sub4` and `sub5` are extensionally equal, but it's easier to prove things 
    -- about `sub5`. For example,
    example (a: ℕ): sub5 (a+2) = a+1 := rfl  -- holds definitionally
    example (a: ℕ): sub5 (succ a) = a := rfl -- ""
    example (a: ℕ): sub5 (a+1) = a := rfl    -- ""

    -- Here's another example of nested pattern matching.
    universe w
    example {α : Type w} (p q : α → Prop) : 
      (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x) 
    | (exists.intro x (or.inl hp)) := or.inl (exists.intro x hp)
    | (exists.intro x (or.inr hq)) := or.inr (exists.intro x hq)
     
    -- The equation compiler can process multiple arguments sequentially.
    def sum_heads : list ℕ → list ℕ → ℕ 
    | [] [] := 0
    | (a::as) [] := a
    | [] (b::bs) := b
    | (a::as) (b::bs) := a + b

    -- Notice that, in the last example, case splitting was applied to both 
    -- the first and second arguments. In contrast, the next few examples split
    -- on the first argument only.
    def band : bool → bool → bool
    | tt a := a
    | ff _ := ff

    def bor : bool → bool → bool
    | tt _ := tt
    | ff a := a

    def {z} cond {a: Type z} : bool → a → a → a
    | tt x y := x
    | ff x y := y

    def head {α : Type u} : list α → option α 
    | [] := none
    | (a::as) := some a

    def tail {α : Type u} : list α → list α 
    | [] := []
    | (a::as) := as

    -- Alternatively, we can put the parameter after the colon...
    def tail2 : Π {α : Type u}, list α → list α 
    | α [] := []
    | α (a :: as) := as
    -- ...still, α plays no role in the case split.

end Sec_8_1


#print "==========================================="
#print "Section 8.2. Wildcards and Overlapping Patterns"
#print " "
-- namespace Sec_8_2
-- end Sec_8_2


#print "==========================================="
#print "Section 8.3. Structural Recursion and Induction"
#print " "

  /-What makes the equation compiler powerful is that it also supports recursive 
    definitions. In the next three sections, we will describe, respectively:
      - structurally recursive definitions
      - well-founded recursive definitions
      - mutually recursive definitions
    Generally speaking, the equation compiler processes input of the following form:

        def foo (a : α) : Π (b : β), γ
        | [patterns₁] := t₁
        ...
        | [patternsₙ] := tₙ 

    Here 
    - `(a : α)` is a sequence of parameters, 
    - `(b : β)` is the sequence of arguments on which pattern matching takes place,
    - `γ` is any type, which can depend on `a` and `b`. 

    Each line should contain the same number of patterns, one for each element of β. 
    As we have seen, a pattern is either 
    - a variable, 
    - a constructor applied to other patterns, or 
    - an expression that normalizes to something of these forms
    (where the non-constructors are marked with the `[pattern]` attribute). 
    The appearances of constructors prompt case splits, with the arguments to the 
    constructors represented by the given variables. -/

    /-As we saw in the last section, the terms `t₁, ..., tₙ` can make use of any of 
    the parameters `a`, as well as any of the variables that are introduced in the 
    corresponding patterns. What makes recursion and induction possible is that they 
    can also involve recursive calls to `foo`. 
    
    In this section, we will deal with *structural recursion*, in which the 
    arguments to `foo` occurring on the right-hand side of the `:=` are subterms 
    of the patterns on the left-hand side. The idea is that they are structurally 
    smaller, and hence appear in the inductive type at an earlier stage. -/
    
    -- Here are some examples of structural recursion from the last chapter, 
    -- now defined using the equation compiler:

namespace hidden
     
    inductive nat : Type
    | zero : nat
    | succ : nat → nat
    
    namespace nat

    def add : nat → nat → nat
    | m zero := m
    | m (succ n) := succ (add m n)

    local infix ` + ` := add

    theorem add_zero (m : nat) : m + zero = m := rfl

    theorem zero_add : ∀ (m : nat), zero + m = m 
    | zero := rfl
    | (succ m) := congr_arg succ (zero_add m)

    def mult: nat → nat → nat
    | m zero := zero
    | m (succ n) := (mult m n) + m 


    -- QUESTION: why doesn't the following type-check?
/-     theorem zero_add_alt (n : nat) : zero + n = n 
    | zero := rfl
    | (succ m) := congr_arg succ (zero_add_alt m)
 -/
    theorem zero_add_alt : ∀ (n: nat), zero + n = n 
    | zero := by rw [add]
    | (succ m) := by rw [add, zero_add_alt m]


    def add_alt (m : nat) : nat → nat
    | zero := m
    | (succ n) := succ (add_alt n)


    -- (Course-of-value compilation is discussed here.)

    -- Another good example of a recursive definition is the list append function.
    def append {α : Type} : list α → list α → list α 
    | [] ys := ys
    | xs [] := xs
    | (x::xs) ys := x :: append xs ys

    example : append [1, 2, 3] [4, 5] = [1,2,3,4,5] := rfl

    end nat

end hidden


#print "==========================================="
#print "Section 8.4. Well-Founded Recursion and Induction"
#print " "

namespace Sec_8_4

end Sec_8_4


#print "==========================================="
#print "Section 8.5. Mutual Recursion"
#print " "

namespace Sec_8_5

end Sec_8_5


#print "==========================================="
#print "Section 8.6. Dependent Pattern Matching"
#print " "

namespace Sec_8_6

end Sec_8_6


#print "==========================================="
#print "Section 8.7. Inaccessible Terms"
#print " "

namespace Sec_8_7

end Sec_8_7


#print "==========================================="
#print "Section 8.8. Match Expressions"
#print " "

namespace Sec_8_8

end Sec_8_8


#print "==========================================="
#print "Section 8.9. Exercises"
#print " "

namespace Sec_8_9

end Sec_8_9


