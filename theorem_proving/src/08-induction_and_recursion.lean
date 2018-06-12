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
    -- todo: prove `sub4 (a+1) = a`


end Sec_8_1


#print "==========================================="
#print "Section 8.2. Wildcards and Overlapping Patterns"
#print " "

namespace Sec_8_2

end Sec_8_2


#print "==========================================="
#print "Section 8.3. Structural Recursion and Induction"
#print " "

namespace Sec_8_3

end Sec_8_3


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


