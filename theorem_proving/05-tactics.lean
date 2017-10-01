-- Chapter 5 Tactics


#print "=================================="
#print "Section 5.1"
#print " "

/- In this chapter, we describe an alternative approach to constructing proofs, using tactics. 
   A proof term is a representation of a mathematical proof; tactics are commands, or 
   instructions, that describe how to build such a proof. Informally, we might begin a 
   mathematical proof by saying "to prove the forward direction, unfold the definition, apply 
   the previous lemma, and simplify." Just as these are instructions that tell the reader how 
   to find the relevant proof, tactics are instructions that tell Lean how to construct a proof 
   term. They naturally support an incremental style of writing proofs, in which users decompose
   a proof and work on goals one step at a time. -/

/- We will describe proofs that consist of sequences of tactics as "tactic-style" proofs, 
   to contrast with the ways of writing proof terms we have seen so far, which we will call 
   "term-style" proofs. Each style has its own advantages and disadvantages. For example, 
   tactic-style proofs can be harder to read, because they require the reader to predict or 
   guess the results of each instruction. But they can also be shorter and easier to write. 
   Moreover, tactics offer a gateway to using Lean's automation, since automated procedures 
   are themselves tactics. -/


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

  /- You can write a tactic script incrementally. If you run Lean on an incomplete tactic 
     proof bracketed by begin and end, the system reports all the unsolved goals that remain. 
     If you are running Lean with its Emacs interface, you can see this information by putting 
     your cursor on the end symbol, which should be underlined. In the Emacs interface, there 
     is another extremely useful trick: if you put your cursor on a line of a tactic proof and 
     press `C-c C-g`, Lean will show you the goal that remains at the end of the line. -/

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

  -- A variant of `apply` called `fapply` is more aggressive in creating new subgoals for args.
  example : ∃ a : ℕ,  a = a :=
  begin
    fapply exists.intro, -- Creates two goals:  (1) provide a natural number a, 
    exact 0,             --                     (2) prove the nat you provided satisfies a = a. 
    apply rfl            -- Goal (2) depends on (1); solving the first goal instantiates a 
  end                    -- metavariable in the second.

  -- The `revert` tactic is sort of inverse to `intro`, as this silly example illustrates.
  example (x : ℕ) : x = x :=  
  begin           -- goal is now `x : ℕ ⊢ x = x`
     revert x,    -- goal is now `∀ (x : ℕ), x = x`
     intro y,     -- goal is now `y : ℕ ⊢ y = y`
     reflexivity 
   end
  -- This example is silly because we can simply use `reflexivity` from the start:
  example (x : ℕ) : x = x :=  begin reflexivity end

  -- `revert` can move a hypothesis into the goal, yielding an implication. 
  -- Here's another silly example:
  example (x y : ℕ) (h : x = y) : y = x :=
  begin       -- goal: `x y : ℕ, h : x = y ⊢ y = x`
    revert h, -- goal: `x y : ℕ ⊢ x = y → y = x`
    intro h₁, -- goal: `x y : ℕ, h₁ : x = y ⊢ y = x`
    symmetry, -- goal: `x y : ℕ, h₁ : x = y ⊢ x = y`
    exact h₁  -- (or we could use `assumption`)
  end 

  /- But revert is clever in that it reverts not only an element of the context, but 
     also all subsequent elements of the context that depend on it. 
     You can also revert multiple elements of the context at once:   -/

  example (x y : ℕ) (h : x = y) : y = x :=
  begin         -- goal: `x y : ℕ, h : x = y ⊢ y = x`
    revert x y, -- goal: `⊢ ∀ (x y : ℕ), x = y → y = x`
    intros,     -- goal: `x y : ℕ, h : x = y ⊢ y = x`
    symmetry,   -- goal: `x y : ℕ, h₁ : x = y ⊢ x = y`
    exact h
  end

  /- You can only `revert` an element of the local context; that is, a local variable 
     or hypothesis. But you can replace an arbitrary expression in the goal by a 
     fresh variable using the `generalize` tactic. -/
  example : 3 = 3 :=
  begin                      -- goal:   `⊢ 3 = 3`
    generalize : 3 = x,      -- goal:   `x : ℕ ⊢ x = x`
    revert x,                -- goal:   `⊢ ∀ (x : ℕ), x = x
    intro y,                 -- goal:   `y : ℕ ⊢ y = y
    reflexivity
  end 
end Sec_5_2


#print "==================================="
#print "Section 5.3. More Tactics"
#print " "

namespace Sec_5_3
  /- Some additional tactics are useful for constructing and destructing propositions and data.
     E.g., when applied to the goal p ∨ q, the tactics `left` and `right` are equivalent to 
     `apply or.inl` and `apply or.inr`, respectively. 
     Conversely, the `cases` tactic can be used to decompose a disjunction. -/

  example (p q : Prop) : p ∨ q → q ∨ p :=
  begin
    intro h,             -- goal:  p q : Prop, h : p ∨ q ⊢ q ∨ p
    cases h with hp hq,  -- two goals:  p q : Prop, hp : p ⊢ q ∨ p  (and sim for q ⊢ q ∨ p)
    -- case hp : p
    right, exact hp,
    -- case hq : q
    left, exact hq
  end     


  -- `cases` can also be used to decompose a conjunction.
  example (p q : Prop) : p ∧ q → q ∧ p :=
  begin
    intro h,
    cases h with hp hq,
    constructor, exact hq, exact hp -- could have used: `apply and.intro hq hp`
  end

  -- Here's a demo of these tactics using an example from earlier.
  example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  begin
    apply iff.intro,
    intro h,
      cases h with hp hqr,
      cases hqr with hq hr,
        left, constructor, exact hp, exact hq,
        right, constructor, exact hp, exact hr,
    intro h,
      cases h with hpq hpr,
      cases hpq with hp hq,
        constructor, exact hp, left, exact hq,
      cases hpr with hp hr,
      constructor, exact hp, right, exact hr
  end

  /- `cases` decomposes any element of an inductively defined type; 
    `constructor` applies the first constructor of an inductively defined type;
     `left` and `right` are used with inductively defined types with exactly two constructors. 
  -/   

  -- We can use `cases` and `constructor` with an existential quantifier.
  example (p q : ℕ → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x :=
  begin
    intro h,
    cases h with x px,
    constructor, left, exact px
  end
  /- Here, `constructor` leaves the first component of the existential assertion (i.e., `x`) 
     implicit. It is represented by a metavariable, which we must instantiate. The instantiated
     value is determined by the tactic `exact px`, since `px` has type `p x`. -/

  /- To specify a witness to the exists quantifier explicitly, use the `existsi` tactic: -/
  example (p q : ℕ → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x :=
  begin
    intro h,
    cases h with x px,
    existsi x, left, exact px
  end

  -- Another example:
  example (p q : ℕ → Prop) : (∃ x, p x ∧ q x) → (∃ x, q x ∧ p x) :=
  begin
    intro h,
    cases h with x hpq,
    cases hpq with hpx hqx,
    existsi x,
    split; assumption  -- `;` tells Lean to apply `assumption` to both goals of the conj
  end
  
  /- These tactics can be used on data just as well as propositions. -/

  -- Here they're used to define functions that swap components of product and sum types:
  universes u v
  def swap_pair {α : Type u} {β : Type v} : α × β → β × α :=
  begin
    intro h,
    cases h with ha hb,
    constructor; assumption
  end

  def swap_sum {α : Type u} {β : Type v} : α ⊕ β → β ⊕ α :=
  begin
    intro h,
    cases h with ha hb,
    right, exact ha, left, exact hb
  end

  -- `cases` will do case distinctions on a natural number:
  open nat
  example (P : ℕ → Prop) (h₀ : P 0) (h₁ : ∀ n, P (succ n)) (m : ℕ) : P m :=
  begin
    cases m with m', exact h₀, exact h₁ m'
  end

  -- `contradiction` searches for a contradiction among the current hypotheses:
  example (p q : Prop) : p ∧ ¬ p → q :=
  begin
    intro h,
    cases h with hp hnp,
    contradiction
  end


end Sec_5_3


#print "==================================="
#print "Section 5.4. Structuring Tactic Proofs"
#print " "

namespace Sec_5_4
  /- it is possible to mix term-style and tactic-style proofs, and pass between the two freely. 
     `apply` and `exact` expect arbitrary terms, e.g., using `have`, `show`, etc.
     Conversely, arbitrary terms can use tactic mode by inserting `begin...end`.-/
  example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
  begin
    intro h,
    exact
      have hp : p, from h.left,
      have hqr : q ∨ r, from h.right,
      show p ∧ q ∨ p ∧ r,
      begin
        cases hqr with hq hr,
        left, split; assumption,   -- alternatively `exact or.inl ⟨hp, hq⟩`
        right, split; assumption   -- alternatively `exact or.inr ⟨hp, hr⟩` 
      end
  end
  -- Here's a more natural example.
  example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  begin
    apply iff.intro,
      intro h,
      cases h.right with hq hr,
        exact or.inl ⟨h.left, hq⟩,
        exact or.inr ⟨h.left, hr⟩,
      intro h,
      cases h with hpq hpr,
        exact ⟨hpq.left, or.inl hpq.right⟩,
        exact ⟨hpr.left, or.inr hpr.right⟩
  end
 
  /- There is also a `show` tactic, which is analogous to the `show` keyword in a proof term. 
     The `show` tactic declares the type of the goal that is about to be solved, while 
     remaining in tactic mode. And, in tactic mode `from` is an alternative name for `exact`.  -/
  example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  begin
    apply iff.intro,
      intro h,
      cases h.right with hq hr,
        show p ∧ q ∨ p ∧ r,
          from or.inl ⟨h.left, hq⟩,  -- alternatively, { left, split, exact h.left, assumption },
        show p ∧ q ∨ p ∧ r,
          from or.inr ⟨h.left, hr⟩,
      intro h,
      cases h with hpq hpr,
        show p ∧ (q ∨ r),
          from ⟨hpq.left, or.inl hpq.right⟩, 
        show p ∧ (q ∨ r),
          from ⟨hpr.left, or.inr hpr.right⟩
  end

  -- `show` can be used to rewrite a goal to something definitionally equivalent.
  example (n : ℕ) : n+1 = nat.succ n := -- could just do `begin reflexivity end`
  begin
    show nat.succ n = nat.succ n, reflexivity
  end

  /- When there are multiple goals, `show` can be used to select which goal to work on.
     Thus, both of these proofs work:    -/
  example (p q : Prop) : p ∧ q → q ∧ p :=
  begin
    intro h, cases h with hp hq, split,
    show q, from hq,
    show p, from hp
  end
  example (p q : Prop) : p ∧ q → q ∧ p :=
  begin
    intro h, cases h with hp hq, split,
    show p, from hp,
    show q, from hq
  end

  -- the `have` tactic introduces a new subgoal, just as when writing proof terms:  
  example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
  begin
    intro h,
    cases h with hp hqr,
    show (p ∧ q) ∨ (p ∧ r),
    cases hqr with hq hr,
      have hpq : p ∧ q, from and.intro hp hq, left, exact hpq,
      have hpr : p ∧ r, from and.intro hp hr, right, exact hpr
  end
  
  
  -- With both `show` and `have` you can omit `from` and stay in tactic mode;
  -- you can also omit the hypothesis label and refer to the given term as `this`.
  example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
  begin
    intro h,
    cases h with hp hqr,
    show (p ∧ q) ∨ (p ∧ r),
    cases hqr with hq hr,
      have : p ∧ q,              -- no label for `p ∧ q`
        exact ⟨hp, hq⟩,
      exact or.inl this,  -- refer to `p ∧ q` as `this`
      have : p ∧ r,
        exact ⟨hp, hr⟩,
      exact or.inr this
  end

  -- alternatively, you can use `:=` instead of `from`
  example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
  begin
    intro h,
    have hp : p := h.left,
    have hqr : q ∨ r := h.right,
    cases hqr with hq hr,
      exact or.inl ⟨hp, hq⟩,
      exact or.inr ⟨hp, hr⟩
  end

  -- the `let` tactic is similar to `have` but introduces local definitions instead
  -- auxiliary facts. It is the tactic analogue of a `let` in a proof term.
  example : ∃ x, x + 2 = 8 :=
  begin
    let a := 6,
    existsi a,
    reflexivity
  end

  -- You can nest `begin...end` blocks within other `begin...end` blocks.
  -- Within a `begin...end` block, nested `begin...end` blocks can be abbrev with curly braces:
  example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  begin
    apply iff.intro,
    { intro h,
      cases h.right with hq hr,
      { exact or.inl ⟨h.left, hq⟩ },
      { exact or.inr ⟨h.left, hr⟩ }
    },
    { intro h,
      cases h with hpq hpr,
      { exact ⟨hpq.left, or.inl hpq.right⟩ },
      { exact ⟨hpr.left, or.inr hpr.right⟩ }
    }
  end

  -- Combining these various mechanisms makes for nicely structured tactic proofs:
  example (p q : Prop) : p ∧ q ↔ q ∧ p :=
  begin
    apply iff.intro,
    { intro h,
      exact ⟨h.right, h.left⟩ 
    },
    { intro h,
      exact ⟨h.right, h.left⟩
    }
  end
  
end Sec_5_4



#print "==================================="
#print "Section 5.5. Tactic Combinators"
#print " "
/- Tactic combinators are operations that form new tactics from old ones. A sequencing combinator
   is already implicit in the comma that appear in a `begin...end` block. -/

namespace Sec_5_5
  example (p q : Prop) (hp : p) : p ∨ q :=
  by { left, assumption }

  -- Here `{ left, assumption }` is functionally equiv to a single tactic which first 
  -- applies `left` and then applies `assumption`.

  -- `t₁; t₂` says "apply t₁ to the current goal and then apply `t₂` to *all* resulting subgoals:
  example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  by split; assumption

  -- The orelse combinator, denoted <|>, applies one tactic, and then backtracks and 
  -- applies another if the first one failed:
  example (p q : Prop) (hp : p) : p ∨ q :=
  by { left, assumption } <|> { right, assumption} -- first one succeeds

  example (p q : Prop) (hq : q) : p ∨ q :=
  by { left, assumption } <|> { right, assumption} -- first one fails, but second succeeds
  


end Sec_5_5


#print "==================================="
#print "Section 5.6. Rewriting"
#print " "
  /- The rewrite tactic provide a basic mechanism for applying substitutions to goals and 
     hypotheses, providing a convenient and efficient way of working with equality. -/

namespace Sec_5_6
  variables (f : ℕ → ℕ) (k : ℕ)

  example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 :=
  begin
    rw h₂, -- replace k with 0
    rw h₁  -- replace f 0 with 0
  end


end Sec_5_6


#print "==================================="
#print "Section 5.7. Using the Simplifier"
#print " "
  /- Whereas `rewrite` is designed as a surgical tool for manipulating a goal, 
     the simplifier offers a more powerful form of automation. A number of identities 
     in Lean's library have been tagged with the `[simp]` attribute, and the simp tactic 
     uses them to iteratively rewrite subterms in an expression. -/

namespace Sec_5_7

end Sec_5_7


#print "==================================="
#print "Section 5.8. Exercises"
#print " "

namespace Sec_5_8

  -- Ex 1. Go back to the exercises in Chapter 3 and Chapter 4 and redo as many as 
  --       you can now with tactic proofs, using also `rw` and `simp` as appropriate.



  -- Ex 2. Use tactic combinators to obtain a one line proof of the following:
  example (p q r : Prop) (hp : p) : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := 
  by exact ⟨or.inl hp, or.inr (or.inl hp), or.inr (or.inr hp)⟩


end Sec_5_8


