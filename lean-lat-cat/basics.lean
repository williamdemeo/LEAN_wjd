namespace llc_basics

  section binary_relations

    def diag_rel (x : ℕ) (y : ℕ) : Prop := (x=y)
    def diag_rel_alt (p : ℕ×ℕ) : Prop := (p.1=p.2)
    #check diag_rel 1 0
    #reduce diag_rel 1 0
    #eval diag_rel_alt ⟨1,1⟩
    #reduce diag_rel_alt ⟨1,1⟩

    -- Expressing the fact that a relation is transitive
    universe u
    variable (α : Type) 
    variable (myrel : α → α → Prop) -- a binary relation
    variable trans_myrel : ∀ {x y z}, myrel x y → myrel y z → myrel x z
    variables a b c : α
    variables (hab: myrel a b) (hbc: myrel b c)

    #check @trans_myrel
    #check trans_myrel hab
    #check trans_myrel hab hbc

    def isTransitive (r : α → α → Prop) : Prop := ∀ (x y z : α), r x y → r y z → r x z

  end binary_relations


  section equivalence_relations -------------------------------------------------------
    
    universe u
    variables (α β : Type u)
    variable e_rel : α → α → Prop
    variable refl_e_rel : ∀ x, e_rel x x 
    variable symm_e_rel : ∀ {x y}, e_rel x y → e_rel y x
    variable trans_e_rel : ∀ {x y z}, e_rel x y → e_rel y z → e_rel x z

    example (a b c d : α) (hab : e_rel a b) (hcb : e_rel c b) (hcd : e_rel c d) : e_rel a d :=
      trans_e_rel (trans_e_rel hab (symm_e_rel hcb)) hcd

    section equality -------------------------
      -- Lean's built-in equality relation is denoted by `eq`
      -- Of course, it's reflexive, symmetric, and transitive
      #check @eq.refl.{u} -- `.{u}` tells Lean to instantiate the constants at `Sort u`
      #check @eq.symm.{u}
      #check @eq.trans.{u}

      example (a b c d : α) (hab : a=b) (hcb : c=b) (hcd : c=d) : a = d := 
        eq.trans (eq.trans hab (eq.symm hcb)) hcd


      /- Reflexivity is more powerful than it looks. Recall that the Calculus of
         Constructions treats terms with a common reduct as equal. As a result, some 
         nontrivial identities can be proved by reflexivity. -/
      example (f : α → β) (a : α) : (λx, f x) a = f a := eq.refl _
      example (a : α) (b : β) : (a,b).1 = a := eq.refl _
      example (a : α) (b : β) : (a,b).2 = b := rfl   -- notation: `rfl` means `eq.refl _`

      -- Equality is a congruence relation in that it is preserved by predicates.
      example (a b : α) (p : α → Prop) (h₁: a = b) (h₂ : p a) : p b := eq.subst h₁ h₂

      example (a b : α) (p : α → Prop) (h₁: a = b) (h₂ : p a) : p b := h₁ ▸ h₂  
                                            -- notation `h₁ ▸ h₂` means `eq.subst h₁ h₂`

      -- auxiliary rules defined using eq.subst: congr_arg, congr_fun, congr
      variables a b : α
      variables f g : α → ℕ
      variables (h₁: a = b) (h₂: f = g)

      example: f a = f b := congr_arg f h₁ 
      example: f a = g a := congr_fun h₂ a
      example: f a = g b := congr h₂ h₁


    

    end equality -----------------------------

  end equivalence_relations -----------------------------------------------------------

end llc_basics
