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


--namespace Sec_4_1
  -- Here is an example of how the propositions-as-types correspondence gets put into practice.

-- LEFT OFF HERE --

/-  variables (α : Type) (p q : α → Prop)
  example : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
    assume h : ∀ x : α, p x ∧ q x,
    take y : α,
    show p y, from (h y).left
-/

--end Sec_4_1

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

