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
  -/


end Sec_4_1

#print "=================================="
#print "Section 4.2 Equality"
#print " "

namespace Sec_4_2
end Sec_4_2


#print "=================================="
#print "Section 4.3 Calculational Proofs"
#print " "

namespace Sec_4_3
end Sec_4_3

#print "=================================="
#print "Section 4.4 The Existential Quantifier"
#print " "

namespace Sec_4_4
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

