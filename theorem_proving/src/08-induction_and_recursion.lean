#print "

Chapter 8. Induction and Recursion


THE EQUATION COMPILER

In the previous chapter, we saw that inductive definitions provide a powerful
means of introducing new types in Lean and that the constructors and the 
recursors provide the only means of defining functions on these types. 

By the propositions-as-types correspondence, this means that 

  *induction is the fundamental method of proof*.

Lean provides natural ways of defining recursive functions, performing pattern 
matching, and writing inductive proofs. It allows you to define a function by 
specifying equations that it should satisfy, and it allows you to prove a 
theorem by specifying how to handle various cases that can arise. 
  
Behind the scenes these descriptions are 'compiled' down to primitive recursors, 
using the so-called 'equation compiler.' The *equation compiler* is not part of 
the trusted code base; its output consists of terms that are checked independently 
by the kernel."


#print "
Section 8.1. Pattern Matching
-----------------------------"

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

    #print "The equations used to define these function hold definitionally."

    lemma example1 : sub0 0 = 0 := rfl
    lemma example2 (n: ℕ) : sub0 (succ n) = n := rfl
    lemma example3 : is_zero zero = true := rfl
    lemma example4 : is_zero (sub0 (succ zero))  = true :=rfl
    lemma example5 : is_zero (succ zero) = false := rfl
    lemma example6 (n: ℕ) : ¬ is_zero (n + 3) := not_false -- N.B. you can't use 
                                               -- `¬ false` here, although
    #check not_false                         -- <- this line gives `¬false`
    
    #print example1
    #print example2
    #print example3
    #print example4
    #print example5
    #print example6

    #print "Pattern matching works with any inductive type, such as product and option."
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

    #print "We use pattern matching to define a function, and do a proof by cases."
    def bnot : bool → bool
    | tt := ff
    | ff := tt

    theorem bnot_involutive : ∀ (b:bool), bnot (bnot b) = b 
    | tt := rfl   -- proof that bnot (bnot tt) = tt
    | ff := rfl   -- proof that bnot (bnot ff) = ff

    #print "Pattern matching can also be used to destruct inductively defined props."

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

    #print "See how Lean compiles the function to recursors:"
    #print sub2._main
    #print id_rhs

    #print "The defining equations hold definitionally."
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

    #print "Another example of nested pattern matching."
    universe w
    example {α : Type w} (p q : α → Prop) : 
      (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x) 
    | (exists.intro x (or.inl hp)) := or.inl (exists.intro x hp)
    | (exists.intro x (or.inr hq)) := or.inr (exists.intro x hq)
     
    #print "The equation compiler can process multiple arguments sequentially."
    def sum_heads : list ℕ → list ℕ → ℕ 
    | [] [] := 0
    | (a::as) [] := a
    | [] (b::bs) := b
    | (a::as) (b::bs) := a + b

    
    #print "In the last example, case splitting can be applied to both the first and second
    arguments. In contrast, the next few examples split on the first argument only."

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


#print "Section 8.2. Wildcards and Overlapping Patterns"


#print "Section 8.3. Structural Recursion and Induction

What makes the equation compiler powerful is that it also supports recursive 
definitions. The next three sections describe, respectively,

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
constructors represented by the given variables."

#print "We saw above that the terms `t₁, ..., tₙ` can make use of any of the parameters 
from the sequence `a`, as well as any of the variables that are introduced in the 
corresponding patterns. What makes recursion and induction possible is that the 
terms, `t₁, ..., tₙ`, can also invoke (recursive) calls to `foo`. 
    
In this section, we will deal with *structural recursion*, in which the arguments to 
`foo` occurring on the right-hand side of `:=` are subterms of the patterns on the 
left-hand side. The idea is that they are structurally smaller, and hence appear in 
the inductive type at an earlier stage.
    
Here we look at some examples of structural recursion from the last chapter, but now 
define them using the equation compiler."

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

  #print "(Course-of-value compilation is discussed here.)"

  #print "Another good example of a recursive definition is the list append function."
    def append {α : Type} : list α → list α → list α 
    | [] ys := ys
    | xs [] := xs
    | (x::xs) ys := x :: append xs ys

    example : append [1, 2, 3] [4, 5] = [1,2,3,4,5] := rfl

    end nat

  #print "The next example adds elements of the first list to elements of the second list, 
  until one of the two lists runs out."

    def {u} list_add {α : Type u} [has_add α] : list α → list α → list α 
    | [] _ := []
    | _ [] := []
    | (x::xs) (y::ys) := (x + y) :: list_add xs ys

    -- Note: this is defined this outside of `nat`, so `+` doesn't clash.
    -- QUESTION: How to define this inside `nat`?

    example : list_add [1,2,3] [4,5] = [5,7] := rfl

    #eval list_add [0,1,2,3,4,5,6,7,8] [1,2,3,4,5,6,7,8]

end hidden


#print "Section 8.4. Well-Founded Recursion and Induction

Dependent type theory is powerful enough to encode and justify well-founded recursion. 
Here is the logical background needed to understand how it works.

Lean's std lib defines two predicates, `acc r a` and `well_founded r`, where 

  - `r` is a binary relation on a type `α`

  - `a` is an element of type `α`."

namespace Sec_8_4
  universes u v
  variable α : Sort u
  variable r : α → α → Prop
  #check (acc r: α → Prop)
  #check (well_founded r: Prop)

#print "`acc` is an inductively defined predicate, and `acc r x` is equivalent to 

∀ y, r y x → acc r y 

Think of `r y x` as denoting a kind of order relation `y ≺ x`. Then `acc r x` 
says that `x` is accessible 'from below' in the sense that all its predecessors 
are accessible. In particular, if `x` has no predecessors, it is accessible.
    
Given any type `α`, we can assign a value to each accessible element of `α`, 
recursively, by assigning values to all its predecessors first.

The statement that `r` is a well founded relation over `α`, denoted 
`well_founded r`, means that every element of the type `α` is accessible.
    
By the above considerations, if `r` is a well-founded relation over a type `α`, 
then we have a principle of well-founded recursion on `α`, with respect to `r`.
Indeed, the Lean stdlib defines `well_founded.fix`, which serves that purpose."

  -- Let's assume `r` is well founded:
  variable h: well_founded r
    
  -- Now let's define a variable `C` that represents the "motive" of a 
  -- recursive definition: 
  variable C: α → Sort v

  -- For each element x : α, we would like to construct an element of C x. 
  -- The following function provides an inductive recipe for doing that.
  variable F : Π x, (Π (y: α), r y x → C y) → C x

  -- The function `F` tells us how to construct an element `C x`, given 
  -- we have `C y` for each predecessor `y` of `x`.

  -- Finally, we use `F`, the hypothesis `h` (that `r` is well founded), and 
  -- `well_founded.fix` to define the function that gives `C x` for each `x`.
  def f : Π (x: α), C x := well_founded.fix h F

  /-Note that `well_founded.fix` works equally well as an induction principle. 
    It says that if `≺` is well founded and you want to prove `∀ x, C x`, then
    it suffices to show that for an arbitrary `x`, if we have `∀ y ≺ x, C y`, 
    then we have `C x`.-/

  namespace hidden
  open nat

  #print "The fn `div` defined below is essentially division on `nat` as found in the std lib."

  #print "But first, a division lemma using two functions from the std lib:"
  #check @nat.sub_lt -- ∀ {a b : ℕ}, 0 < a → 0 < b → a - b < a
  #check @nat.lt_of_lt_of_le -- ∀ {n m k : ℕ}, n < m → m ≤ k → n < k

  def div_rec_lemma { x y : ℕ } : 0 < y ∧ y ≤ x → x - y < x :=
    assume h : 0 < y ∧ y ≤ x,
      have hx : 0 < x, from (lt_of_lt_of_le h.left h.right),
      show x - y < x, from sub_lt hx h.left 

  #print "Finally, here's div."
  def div.F (x: ℕ) (f : Π x₁, x₁ < x → ℕ → ℕ) (y: ℕ) : ℕ :=
    if h : 0 < y ∧ y ≤ x then
      f (x - y) (div_rec_lemma h) y + 1 -- the 1st arg is x₁, the 2nd is h: x₁ < x
    else 0

  #print "The equation compiler makes such definitions more convenient. It accepts the following:"
  def div : ℕ → ℕ → ℕ
  | x y :=
    if h : 0 < y ∧ y ≤ x then
      have x - y < x, 
        from sub_lt (lt_of_lt_of_le h.left h.right) h.left,
      div (x - y) y + 1
    else 0

  #print "The defining equation for `div` does not hold definitionally, but the equation is 
  available to `rewrite` and `simp`."
  example (x y : ℕ) :  
    div x y = if 0 < y ∧ y ≤ x then div (x - y) y + 1 else 0 :=
  by rw [div]  -- `simp` would loop here, but `rw` works.

  example (x y : ℕ) (h : 0 < y ∧ y ≤ x) : 
    div x y = div (x - y) y + 1 :=
  by rw [div, if_pos h]

  #print "
  Here's a similar example that converts a natural number into binary (0’s and 1’s). 
  We have to supply the equation compiler with evidence that the recursive call is 
  decreasing, which we do with `sorry`. 
  
  Note how the use of `sorry` here doesn't prevent the bytecode evaluator from 
  evaluating the function successfully."

    def nat_to_bin : ℕ → list ℕ 
    | 0 := [0]
    | 1 := [1]
    | (n+2) := have (n+2)/2 < n+2, from sorry,
               nat_to_bin ((n+2)/2) ++ [n % 2]

    #eval nat_to_bin 8
    -- (n+2) = 8  =>  n = 6
    -- nat_to_bin 4 ++ [6%2]   --> [0]
       -- (n+2) = 4  =>  n=2
       -- nat_to_bin 2 ++ [2%2]   --> [0, 0]
          -- (n+2) = 2  =>  n=0
          -- nat_to_bin 1 ++ [0%2]  --> [0, 0, 0]
          -- nat_to_bin 1 = [1]        
          --  Final answer:            --> [1, 0, 0, 0]


    end hidden

    -- Ackermann's function can be defined directly, because it is justified by 
    -- the well foundedness of the lexicographic order on the natural numbers.

    def ack : ℕ → ℕ → ℕ 
    | 0 y := y+1
    | (x+1) 0 := ack x 1
    | (x+1) (y+1) := ack x (ack (x+1) y)

    #eval ack 3 9

  /-Lean's mechanisms for guessing a well-founded relation and then proving that 
    recursive calls decrease are still in a rudimentary state. They will be 
    improved over time. When they work, they are more convenient for defining 
    functions than using `well_founded.fix` manually. When they don't work,
    the latter is always available as a backup.-/
end Sec_8_4


#print "Section 8.5. Mutual Recursion"
namespace Sec_8_5
-- I already know the material covered in this section... it's easy.
end Sec_8_5


#print "
Section 8.6. Dependent Pattern Matching

The examples of pattern matching considered above are easily written using `cases_on` 
and `rec_on`. However, this is often not the case with indexed inductive families such 
as `vector α n`, since the splits impose constraints on the values of the indices.

Without the equation compiler, we would need a lot of boilerplate code to define very 
simple functions such as map, zip, and unzip using recursors." 

namespace Sec_8_6
  --Consider the tail function, which takes `v : vector α (succ n)` and deletes the first element. 
  -- A first thought might be to use the `cases_on` function:
  universe u
  inductive vector (α : Type u) : ℕ → Type u
  | nil {} : vector 0
  | cons : Π {n}, α → vector n → vector (n+1)

  namespace vector 
    local notation h :: t := cons h t

    #check @vector.cases_on
    -- Π {α : Type u_2} {C : Π (a : ℕ), vector α a → Sort u_1} {a : ℕ} (n : vector α a),
    --   C 0 nil → (Π {n : ℕ} (a : α) (a_1 : vector α n), C (n + 1) (a :: a_1)) → C a n

    #print "But what value should we return in the `nil` case? Something funny is going on. 
    If `v` has type `vector α (succ n)`, it *can't* be nil, but it is not clear how to tell 
    that to `cases_on`.

    One solution is to define an auxiliary function."
  
    def tail_aux {α : Type} {n m : ℕ} (v : vector α m) : m = n + 1 → vector α n :=
      vector.cases_on v
        (assume H : 0 = n + 1, nat.no_confusion H)
        (assume m (a : α) w : vector α m,
          assume H : m + 1 = n + 1,
            nat.no_confusion H (λ H1 : m = n, eq.rec_on H1 w))

    def tail_first_try {α : Type} {n : ℕ} (v : vector α (n+1)) : vector α n := tail_aux v rfl
  #print "In the `nil` case, `m` is instantiated to `0`, and `no_confusion` makes use of the 
  fact that `0 = succ n` cannot occur. Otherwise, `v` is of the form `a :: w`, and we can 
  simply return `w`, after casting it from a vector of length `m` to a vector of length `n`.

  The difficulty in defining `tail` is to maintain the relationships between the indices. 
  The hypothesis `e : m = n + 1` in `tail_aux` is used to communicate the relationship between 
  `n` and the index associated with the minor premise. Moreover, the `zero = n + 1` case is 
  unreachable, and the canonical way to discard such a case is to use `no_confusion`."

  end vector


  #print "The `tail` function is, however, easy to define using recursive equations, and the 
  equation compiler generates all the boilerplate code automatically for us. Here are a 
  number of similar examples."
  namespace vector
    local notation h :: t := cons h t
    def head {α : Type} : Π {n}, vector α (n+1) → α
    | n (h :: t) := h

    def tail {α : Type} : Π {n}, vector α (n+1) → vector α n
    | n (h :: t) := t

    lemma eta {α : Type} : 
    ∀ {n} (v : vector α (n+1)), head v :: tail v = v
    | n (h :: t) := rfl

    def map {α β γ : Type} (f : α → β → γ) : Π {n}, vector α n → vector β n → vector γ n
    | 0     nil       nil       := nil
    | (n+1) (a :: va) (b :: vb) := f a b :: map va vb

    def zip {α β : Type} : Π {n}, vector α n → vector β n → vector (α × β) n
    | 0     nil       nil       := nil
    | (n+1) (a :: va) (b :: vb) := (a, b) :: zip va vb

    #print head
    #print tail
    #print eta
    #print map
    #print zip

  end vector

#print "Note that we can omit recursive equations for 'unreachable' cases such as `head nil`. 

The automatically generated definitions for indexed families are far from 
straightforward, as the following examples demonstrate."
  namespace vector
  local notation h :: t := cons h t

  def vector.map {α β γ : Type} (f : α → β → γ): Π {n : nat}, vector α n → vector β n → vector γ n
    | 0     nil     nil     := nil
    | (n+1) (a::va) (b::vb) := f a b :: vector.map va vb

    #print map
    #print map._main

   end vector

#print "The `map` function is even more tedious to define by hand than the `tail` function. 
TODO: We encourage you to try it, using `rec_on`, `cases_on` and `no_confusion`."

end Sec_8_6

#print "
Section 8.7. Inaccessible Terms
===============================

Sometimes an argument in a dependent pattern matching is not essential to the definition, 
but nonetheless has to be included to specialize the type of the expression appropriately. 
Lean allows users to mark such subterms as *inaccessible* for pattern matching. These 
annotations are essential, for example, when a term occurring in the left-hand side is 
neither a variable nor a constructor application, because such terms are not suitable targets 
for pattern matching. We can view such inaccessible terms as 'don't care' components of the 
patterns. You can declare a subterm inaccessible by writing `.(t)`. If the inaccessible term 
can be inferred, you can also write `._`.

The following example can be found in [GoMM06]_. We declare an inductive type that defines the 
property of 'being in the image of `f`'. You can view an element of the type `image_of f b` 
as evidence that `b` is in the image of `f`, whereby the constructor `imf` is used to build 
such evidence. We can then define any function `f` with an 'inverse' which takes anything 
in the image of `f` to an element that is mapped to it. The typing rules forces us to write 
`f a` for the first argument, but this term is neither a variable nor a constructor application, 
and plays no role in the pattern-matching definition. 

To define the function `inverse` below, we *have to* mark `f a` inaccessible.

"
namespace Sec_8_7

  namespace example_image_of

    variables {α β : Type}

    inductive image_of (f : α → β) : β → Type
    | imf : Π (a: α), image_of (f a)

    open image_of

    def inverse_of {f : α → β} : Π (b: β), image_of f b → α 
    | .(f a) (imf .(f) a) := a

    #print "In the example above, the inaccessible annotation makes it clear that `f` is 
    *not* a pattern matching variable.

    Inaccessible terms can be used to clarify and control definitions that make use of dependent 
    pattern matching. Consider the function defining the addition of any two vectors of elements 
    of a type that has an associated addition function."

  end example_image_of

  namespace example_vector_addition
    universe u

    inductive vector (α : Type u) : ℕ → Type u
    | nil {} : vector 0
     | cons : Π {n : ℕ}, α → vector n → vector (n+1) 

    namespace vector 
      local notation h :: t := cons h t
      variable {α : Type u}

      def add [has_add α] : Π {n : ℕ}, vector α n → vector α n → vector α n 
      | 0      nil             nil               := nil
      | (n+1) (cons a v) (cons b w) := cons (a + b) (add v w)


    end vector 


  #print "The argument `{n : ℕ}` has to appear after the colon, because it cannot be held 
  fixed throughout the definition. When implementing this definition, the equation compiler 
  starts with a case distinction as to whether the first argument is `0` or of the form `n+1`. 
  This is followed by nested case splits on the next two arguments, and in each case the equation compiler rules out the cases are not compatible with the first pattern.

But, in fact, a case split is not required on the first argument; the ``cases_on`` eliminator for ``vector`` automatically abstracts this argument and replaces it by ``0`` and ``n + 1`` when we do a case split on the second argument. Using inaccessible terms, we can prompt the equation compiler to avoid the case split on ``n``:
"
  end example_vector_addition



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



/- [GoMM06] Healfdene Goguen, Conor McBride, and James McKinna. 'Eliminating dependent pattern 
matching. In Kokichi Futatsugi, Jean-Pierre Jouannaud, and José Meseguer, editors, 
Algebra, Meaning, and Computation, Essays Dedicated to Joseph A. Goguen."
 -/