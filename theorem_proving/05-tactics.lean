-- Chapter 5 Tactics


#print "=================================="
#print "Section 5.1"
#print " "

/- In this chapter, we describe an alternative approach to constructing proofs, using tactics. A proof term is a representation of a mathematical proof; tactics are commands, or instructions, that describe how to build such a proof. Informally, we might begin a mathematical proof by saying "to prove the forward direction, unfold the definition, apply the previous lemma, and simplify." Just as these are instructions that tell the reader how to find the relevant proof, tactics are instructions that tell Lean how to construct a proof term. They naturally support an incremental style of writing proofs, in which users decompose a proof and work on goals one step at a time.

We will describe proofs that consist of sequences of tactics as "tactic-style" proofs, to contrast with the ways of writing proof terms we have seen so far, which we will call "term-style" proofs. Each style has its own advantages and disadvantages. For example, tactic-style proofs can be harder to read, because they require the reader to predict or guess the results of each instruction. But they can also be shorter and easier to write. Moreover, tactics offer a gateway to using Lean's automation, since automated procedures are themselves tactics. -/


#print "==================================="
#print "Section 5.1. Entering Tactic Mode"
#print " "

namespace Sec_5_1
  theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := 
  begin
    apply and.intro, exact hp, 
    apply and.intro, exact hq, exact hp
  end 

  -- You can see the resulting proof term with the #print command:
  #print test

/- You can write a tactic script incrementally. If you run Lean on an incomplete tactic proof bracketed by begin and end, the system reports all the unsolved goals that remain. If you are running Lean with its Emacs interface, you can see this information by putting your cursor on the end symbol, which should be underlined. In the Emacs interface, there is another extremely useful trick: if you put your cursor on a line of a tactic proof and press `C-c C-g`, Lean will show you the goal that remains at the end of the line. -/

end Sec_5_1

#print "==================================="
#print "Section 5.2. Basic Tactics"
#print " "

/- In addition to `apply` and `exact`, another useful tactic is `intro`, which 
   introduces a hypothesis. Here's an example of an identity from propositional 
   logic that we proved Section 3.6, now proved using tactics. -/

namespace Sec_5_2

  example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  begin
    apply iff.intro,
      intro h,
      apply or.elim (and.right h),
        intro hq,
        apply or.inl,
        apply and.intro (and.left h) hq,
        intro hr,
        apply or.inr,
        apply and.intro (and.left h) hr,
      intro h,
      apply or.elim h,
        intro hpq,
        apply and.intro hpq.left (or.inl hpq.right),
      intro hpr,
      apply and.intro hpr.left (or.inr hpr.right)
  end 


  -- The intro command can more generally be used to introduce a variable of any type:

  example (α : Type) : α → α :=
  begin
    intro a, exact a
  end

  example (α : Type) : ∀ x : α, x = x :=
  begin
    intro x, exact eq.refl x
  end

  -- `intro` has a plural form, `intros`, that takes a list of names. 

  example : ∀ a b c : ℕ, a = b → a = c → b = c :=
  begin
    intros a b c h₁ h₂,
    exact eq.trans (eq.symm h₁) h₂
  end
    
  /- The `assumption` tactic looks through the assumptions in context of the current goal, 
     and if there is one matching the conclusion, it applies it. -/

  variable α : Type
  variables x y z w : α

  example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w :=
  begin
    apply eq.trans h₁,
    apply eq.trans h₂,
    assumption
  end

  -- The `assumption` tactic will unify metavariables in the conclusion if necessary:

  example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w :=
  begin
    apply eq.trans, assumption,
    apply eq.trans, assumption,
    assumption
  end

  -- We could use `intros` to introduce the variables and hypotheses automatically:

  example : ∀ a b c : ℕ, a = b → a = c → b = c :=
  begin
    intros,
    apply eq.trans,
    apply eq.symm,
    assumption,
    assumption
  end

  /- `reflexivity`, `symmetry`, `transitivity`
     Using reflexivity, for example, is more general than `apply eq.refl`, 
     because it works for any relation that has been tagged with the `refl` attribute. 
     (Attributes will be discussed in Section 6.4.) 
     `reflexivity` is abbreviated `refl`. -/

  example  (y : ℕ) : (λ x : ℕ, 0) y = 0 := begin refl end

  example (x : ℕ) : x ≤ x := begin refl end

  example : ∀ a b c : ℕ, a = b → a = c → b = c :=
  begin
    intros, transitivity, symmetry, assumption, assumption
  end

  -- Instead of typing `assumption` twice, we can use the `repeat` combinator:
  example : ∀ a b c : ℕ, a = b → a = c → b = c :=
  begin
    intros, transitivity, symmetry, repeat { assumption }
  end

  -- the curly braces introduce a new tactic block; equivalent to a nested `begin ... end` pair.

  -- A variant of `apply` called `fapply` that is more aggressive in creating new subgoals:
  example : ∃ a : ℕ,  a = a :=
  begin
    fapply exists.intro,
    exact 0,
    apply rfl
  end
  
  /- `fapply exists.intro` creates two goals: (1) provide a natural number a, (2) prove 
     that a = a. The second goal depends on the first; solving the first goal instantiates 
     a metavariable in the second. -/

  -- The `revert` tactic is, in a sense, an inverse to `intro`.
  example (x : ℕ) : x = x :=  begin revert x, intro y, reflexivity end

  



end Sec_5_2



#print "==================================="
#print "Section 5.3. More Tactics"
#print " "

namespace Sec_5_3

end Sec_5_3


#print "==================================="
#print "Section 5.4. Structuring Tactic Proofs"
#print " "

namespace Sec_5_4

end Sec_5_4


#print "==================================="
#print "Section 5.5. Tactic Combinators"
#print " "

namespace Sec_5_5

end Sec_5_5


#print "==================================="
#print "Section 5.6. Rewriting"
#print " "

namespace Sec_5_6

end Sec_5_6


#print "==================================="
#print "Section 5.7. Using the Simplifier"
#print " "

namespace Sec_5_7

end Sec_5_7


#print "==================================="
#print "Section 5.8. Exercises"
#print " "

namespace Sec_5_8

end Sec_5_8


