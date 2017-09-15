-- Chapter 4 Quantifiers and Equality


#print "=================================="
#print "Section 4.1 The Universal Quantifier"
#print " "
/- Notice that if α is any type, we can represent a unary predicate p on α as an 
   object of type α → Prop. In that case, if x : α, then p x denotes the assertion 
   that p holds of x. Similarly, an object r : α → α → Prop denotes a binary 
   relation on α: if x y : α, then r x y denotes the assertion that x is related to y.

   The universal quantifier, ∀ x : α, p x is supposed to denote the assertion that 
   "for every x : α, p x" holds. As with the propositional connectives, in systems of 
   natural deduction, "forall" is governed by an introduction and elimination rule. 

   Informally, the introduction rule states: 
   Given a proof of p x, in a context where x : α is arbitrary, we obtain a proof 
   ∀ x : α, p x.

   The elimination rule states:
   Given a proof ∀ x : α, p x and any term t : α, we obtain a proof of p t.

   The propositions-as-types interpretation now comes into play. Remember the introduction 
   and elimination rules for Pi types:

   Introduction Rule for Pi types:
   Given a term t of type β x, in a context where x : α is arbitrary, we have 
   (λ x : α, t) : Π x : α, β x.

   Elimination rule for Pi types:
   Given a term s : Π x : α, β x and any term x : α, we have s x : β x.

   If p x has type Prop, and if we replace Π x : α, β x with ∀ x : α, p x, then we can
   read these as the correct rules for building proofs involving the universal quantifier.

   The Calculus of Constructions therefore identifies Π and ∀ in this way.
   If p is any expression, ∀ x : α, p is simply alternative notation for Π x : α, p, 
   with the idea that the former is more natural than the latter in cases where p 
   is a proposition. 

   Typically, the expression p will depend on x : α. Recall that, in the case of ordinary 
   function spaces, we could interpret α → β as the special case of Π x : α, β in which β 
   does not depend on x. Similarly, we can think of an implication p → q between propositions 
   as the special case of ∀ x : p, q in which the expression q does not depend on x. 
-/


namespace Sec_4_1

  -- Example: how the propositions-as-types correspondence is used in practice.
  namespace example1  
    variables (α : Type) (p q : α → Prop)
    example : (∀ x : α, p x ∧ q x) → ∀ y : α, p y  :=
    assume h : ∀ x : α, p x ∧ q x,
    assume y : α,
    show p y, from (h y).left

    -- alternative version of the last example
    example : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
      λ (h : ∀ x : α, p x ∧ q x) (y : α), and.left (h y)

  end example1


  -- Example: expressing the fact that a relation r is transitive.
  namespace example2
    variables (α : Type) (r : α → α → Prop)
    variable trans_r : ∀ x y z : α, r x y → r y z → r x z
    variables a b c : α
    variables (h₁ : r a b) ( h₂ : r b c)
    #check trans_r                 -- ∀ (x y z : α), r x y → r y z → r x z
    #check trans_r a b c           -- r a b → r b c → r a c
    #check trans_r a b c h₁        -- r b c → r a c
    #check trans_r a b c h₁ h₂     -- r a c

  end example2

  -- Example: impicit parameters
  namespace example3
    /- It can be tedious to supply the arguments a b c, when they can be inferred 
      from hab hbc. For that reason, it is common to make these arguments implicit: -/
      universe u
      variables (α : Type) (r : α → α → Prop)
      variable trans_r : ∀ {x y z : α}, r x y → r y z → r x z
      variables a b c : α
      variables (h₁ : r a b) (h₂ : r b c)
      #check trans_r             -- trans_r : r ?M_1 ?M_2 → r ?M_2 ?M_3 → r ?M_1 ?M_3
      #check trans_r h₁          -- trans_r h₁ : r b ?M_1 → r a ?M_1
      #check trans_r h₁ h₂       -- trans_r h₁ h₂ : r a c

      -- The advantage is that we can now write `trans_r h₁ h₂` as a proof of `r a c`.
  
  end example3
  
  -- Example: elementary reasoning with an equivalence relation.
  namespace example4
  
    variables (α : Type) (r : α → α → Prop)
    variable refl_r : ∀ {x : α}, r x x
    variable symm_r : ∀ {x y : α}, r x y → r y x
    variable trans_r : ∀ {x y z : α}, r x y → r y z → r x z

    example (a b c d : α) (h₁ : r a b) (h₂ : r c b) (h₃ : r c d) : r a d :=
      have h₄ : r b c, from (symm_r h₂),
      have h₅ : r a c, from (trans_r h₁ h₄),
      show r a d, from (trans_r h₅ h₃)

    -- after working out a proof in simple steps, we can make it more concise:
    example (a b c d : α) (h₁ : r a b) (h₂ : r c b) (h₃ : r c d) : r a d :=
      (trans_r (trans_r h₁ (symm_r h₂)) h₃)



  end example4


  /- It is the typing rule for Pi types, and the universal quantifier in particular, 
     that distinguishes Prop from other types. Suppose we have α : Sort i and 
     β : Sort j, where the expression β may depend on a variable x : α. 
     Then Π x : α, β is an element of Type (imax i j), where imax i j is the maximum 
     of i and j if j is not 0, and 0 otherwise.

     The idea is as follows: If j is not 0, then Π x : α, β is an element of 
     Sort (max i j). In other words, the type of dependent functions from α to β 
     "lives" in the universe whose index is the maximum of i and j. Suppose, however,
     that β is of Sort 0, that is, an element of Prop. In that case, Π x : α, β is 
     an element of Sort 0 as well, no matter which type universe α lives in. 
     In other words, if β is a proposition depending on α, then ∀ x : α, β is 
     again a proposition. This reflects the interpretation of Prop as the type of 
     propositions rather than data, and it is what makes Prop *impredicative*.

     Impredicativity of Prop Type:
     If α is a type, we can form the type α → Prop of all predicates on α (aka 
     the "power type" of α). The impredicativity of Prop means that we can form 
     propositions (i.e., inhabitants of Prop) that quantify over α → Prop. In 
     particular, we can define predicates on α by quantifying over all predicates 
     on α; this is the type of circularity that was once considered problematic.
  -/


end Sec_4_1

#print "=================================="
#print "Section 4.2 Equality"
#print " "
  /- Chapter 7 explains how equality is defined from primitives of Lean's 
     logical framework. Here we just see how to use equality. -/

  -- Of course, equality is an equivalence relation:

namespace Sec_4_2

  namespace example1
    #check eq.refl          -- ∀ (a : ?M_1), a = a
    #check eq.symm          -- ?M_2 = ?M_3 → ?M_3 = ?M_2
    #check eq.trans         -- ?M_2 = ?M_3 → ?M_3 = ?M_4 → ?M_2 = ?M_4

    /- Output is easier to read if we have Lean instantiate implicit arguments at a
       particular universe u. -/

    universe u

    #check @eq.refl.{u}   -- ∀ {α : Sort u} (a : α), a = a
    #check @eq.symm.{u}   -- ∀ {α : Sort u} {a b : α}, a = b → b = a
    #check @eq.trans.{u}  -- ∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

  end example1


  /- Reflexivity is more powerful than it looks. Recall that the Calculus of
     Constructions treats terms with a common reduct as equal. As a result, some 
     nontrivial identities can be proved by reflexivity. -/

  namespace example2
    universe u
    variables (α β : Type u)
    example (f : α → β) (a : α) : (λ x : α, f x) a = f a := eq.refl _
    example (a₁ : α) (a₂ : α) : (a₁, a₂).1 = a₁ := eq.refl _
    example : 2 + 3 = 5 := eq.refl _

  -- This feature is so important Lean defines a notation `rfl` for `eq.refl _`.
    example (f : α → β) (a : α) : (λ x : α, f x) a = f a := rfl

  end example2

  /- Equality is more than just an equivalence relation. It is a congruence 
     (the smallest congruence) in every congruence lattice; thus, it has the 
     property that every assertion respects the equivalence.  -/

  /- For instance, given `h₁ : a = b` and `h₂ : p a`, we can construct a proof 
     for `p b` using substitution: `eq.subst h₁ h₂`. -/
  namespace example3
    universe u
    example (α : Type u) (a₁ a₂ : α) (p : α → Prop)
      (h₁ : a₁ = a₂) (h₂ : p a₁) : p a₂ := eq.subst h₁ h₂

  -- Lean has a shorthand for eq.subst as well; it's ▸, as shown here.
    example (α : Type u) (a₁ a₂ : α) (p : α → Prop)
      (h₁ : a₁ = a₂) (h₂ : p a₁) : p a₂ := h₁ ▸ h₂
  
  
  end example3


  /- `eq.subst` is used to define the following auxiliary rules, which carry out 
     more explicit substitutions. They deal with applicative terms (of form s t). 
     Specifically, we use `congr_arg` to replace the argument, `congr_fun` to
     replace the term that is being applied, and `congr` to replace both at once. -/

  namespace example4
    variable α : Type
    variables a₁ a₂ : α
    variables f g : α → ℕ
    variable h₁ : a₁ = a₂
    variable h₂ : f = g

    example : f a₁ = f a₂ := congr_arg f h₁
    example : f a₁ = g a₁ := congr_fun h₂ a₁
    example : f a₁ = g a₂ := congr h₂ h₁
    
  end example4

  namespace example5
    variables a b c d : ℤ
    example : a + 0 = a := add_zero a
    example : 0 + a = a := zero_add a
    example : a * 1 = a := mul_one a
    example : 1 * a = a := one_mul a
    example : -a + a = 0 := neg_add_self a
    example : a + -a = 0 := add_neg_self a
    example : a - a = 0 := sub_self a
    example : a + b = b + a := add_comm a b
    example : a + b + c = a + (b + c) := add_assoc a b c
    example : a * b = b * a := mul_comm a b
    example : a * b * c = a * (b * c) := mul_assoc a b c
    example : a * (b + c) = a * b + a * c := mul_add a b c
    example : a * (b + c) = a * b + a * c := left_distrib a b c
    example : (a + b) * c = a * c + b * c := add_mul a b c
    example : (a + b) * c = a * c + b * c := right_distrib a b c
    example : a * (b - c) = a * b - a * c := mul_sub a b c
    example : (a - b) * c = a * c - b * c := sub_mul a b c
  end example5

  /- Identities likes these work in arbitrary instances of the relevant 
     algebraic structures, using the type class mechanism described in Chapter 10. 
     Chapter 6 provides shows how to find theorems like this in the library. -/

  namespace example6
    example (x y z : ℕ) : x * (y + z) = x * y + x * z := sorry
    example (x y z : ℕ) : x * (y + z) = x * y + x * z := sorry
    example (x y z : ℕ) : x + y + z = x + (y + z) := sorry

    example (x y : ℕ) : (x + y) * (x + y) = x * x + y * x + x * y + y * y := sorry
  end example6


  /- The 2nd implicit parameter to ▸ provides the context in which the subst occurs.
     This parameter has type α → Prop, so inferring this predicate requires an 
     instance of *higher-order unification*.  The problem of determining whether 
     a higher-order unifier exists is undecidable, and Lean can at best provide 
     imperfect and approximate solutions. As a result, eq.subst doesn't always do 
     what you want; this is discussed in greater detail in Section 6.10. -/

  /- IMPORTANT (for project proposal)
     Because equational reasoning is so common and important, Lean provides a 
     number of mechanisms to carry it out more effectively. The next section offers 
     syntax that allow you to write calculational proofs in a more natural and 
     perspicuous way. But, more importantly, equational reasoning is supported by 
     a term rewriter, a simplifier, and other kinds of automation. The term rewriter 
     and simplifier are described briefly in the next setion, and then in greater 
     detail in the next chapter. -/



end Sec_4_2


#print "=================================="
#print "Section 4.3 Calculational Proofs"
#print " "
  /- A calculational proof (or "proof sequence") is a chain of intermediate 
     results meant to be composed by basic principles such as the transitivity 
     of equality. In Lean, such proofs start with the keyword `calc`, and have 
     the following syntax:

           calc
             <expr>_0  'op_1'  <expr>_1  ':'  <proof>_1
             '...'   'op_2'  <expr>_2  ':'  <proof>_2
              ...
             '...'   'op_n'  <expr>_n  ':'  <proof>_n

     where each `<proof>_i` is a proof for `<expr>_{i-1} op_i <expr>_i`. -/

namespace Sec_4_3
  namespace example1
    variables a b c d e : ℕ
    variables h₁ : a = b
    variables h₂ : b = c + 1
    variables h₃ : c = d
    variables h₄ : e = 1 + d

  theorem T : a = e :=
    calc
      a     = b     : h₁
        ... = c + 1 : h₂
        ... = d + 1 : congr_arg _ h₃
        ... = 1 + d : add_comm d ( 1 : ℕ)
        ... = e     : eq.symm h₄


  end example1

  /- The style is most effective when used in conjunction with `simp` and `rewrite` 
     tactics, discussed in greater detail in Ch 5. -/

  namespace example2
    variables a b c d e : ℕ
    variables h₁ : a = b
    variables h₂ : b = c + 1
    variables h₃ : c = d
    variables h₄ : e = 1 + d

  include h₁ h₂ h₃ h₄
  theorem T₁ : a = e :=
    calc
      a     = b      : h₁
        ... = c + 1  : h₂
        ... = d + 1  : by rw h₃
        ... = 1 + d  : by rw add_comm
        ... = e      : by rw h₄

  -- Rewrites can applied sequentially, so the above can be shortened as follows:
  theorem T₂ : a = e :=
    calc
      a     = d + 1 : by rw [h₁, h₂, h₃]
        ... = 1 + d : by rw add_comm
        ... = e     : by rw h₄

  -- ...or even this
  theorem T₃ : a = e := by rw [h₁, h₂, h₃, add_comm, h₄]

  end example2

end Sec_4_3

#print "=================================="
#print "Section 4.4 The Existential Quantifier"
#print " "

  /- Finally, consider the existential quantifier, which can be written as either 
     `exists x : α, p x` or `∃ x : α, p x`. Both versions are actually abbreviations
     for the expression `Exists (λ x : α, p x)`, defined in Lean's library. -/

  /- As usual, the library includes both an intro and elim rule for exists. 
     INTRO: to prove `∃ x : α, p x`, it suffices to provide a term `t : α` and 
     a proof of `p t`. -/

namespace Sec_4_4

  namespace example1
    open nat
    example : ∃ x : ℕ, x > 0 := 
      have h : 1 > 0, from zero_lt_succ 0, exists.intro 1 h
    
    example (x : ℕ) (h : x > 0) : ∃ y : ℕ, y < x := exists.intro 0 h
    
    example (x y z : ℕ) (h₁ : x < y) (h₂ : y < z) : ∃ w, x < w ∧ w < z :=
      exists.intro y (and.intro h₁ h₂)

    #check @exists.intro

  end example1

  namespace example2
    variable g : ℕ → ℕ → ℕ
    variable h₁ : g 0 0 = 0

    theorem g₁ : ∃ x, g x x = x := ⟨0, h₁⟩
    theorem g₂ : ∃ x, g x 0 = x := ⟨0, h₁⟩
    theorem g₃ : ∃ x, g 0 0 = x := ⟨0, h₁⟩
    theorem g₄ : ∃ x, g x x = 0 := ⟨0, h₁⟩

    set_option pp.implicit true    -- (to display implicit arguments)
    #check g₁
    #check g₂
    #check g₃
    #check g₄
  
  
  end example2

  namespace example3

  end example3

  namespace example4

  end example4

end Sec_4_4

#print "=================================="
#print "Section 4.5 More on the Proof Language"
#print " "

namespace Sec_4_5
end Sec_4_5

#print "=================================="
#print "Section 4.6 Exercises"
#print " "

namespace Sec_4_6
end Sec_4_6

