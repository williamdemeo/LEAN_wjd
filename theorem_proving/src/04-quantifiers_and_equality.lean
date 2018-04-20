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
    #print congr_arg
    #print congr
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
    example (x y z : ℕ) : x * (y + z) = x * y + x * z := mul_add x y z
      
    example (x y z : ℕ) : x + y + z = x + (y + z) := add_assoc x y z

    example (x y : ℕ) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=  --sorry
      have h₁ : (x + y) * (x + y) = x * (x + y) + y * (x + y), from add_mul x y (x + y),
      have h₃ : x * (x + y)  = x * x + x * y, from mul_add x x y,
      have h₄ : y * (x + y) = y * x + y * y, from mul_add y x y,
      calc
        (x + y) * (x + y) = x * (x + y) + y * (x + y) : by rw h₁
                      ... = (x*x + x*y) + (y*x + y*y) : by rw [h₃, h₄]
                      ... = x*x + y*x + x*y + y*y   : by simp

    -- the same example, proved in a different way:
    example (x y : ℕ) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
      have h₁ : (x + y) * (x + y) = (x + y) * x + (x + y) * y, from mul_add (x + y) x y,
      have h₂ : (x + y) * (x + y) = x * x + y * x + (x * y + y * y), 
        from (add_mul x y x) ▸ (add_mul x y y) ▸ h₁,
      h₂.trans (add_assoc (x * x + y * x) (x * y) (y * y)).symm

    -- the same example, proved in yet another way:
    example (x y : ℕ) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
      calc 
        (x + y) * (x + y) = (x + y) * x + (x + y) * y       : by rw mul_add
                      ... = x * x + y * x + (x + y) * y     : by rw add_mul
                      ... = x * x + y * x + (x * y + y * y) : by rw add_mul
                      ... = x * x + y * x + x * y + y * y   : by rw ←add_assoc
                                         -- we need ← here since we're using 
                                         --   x + (y + z) = (x + y) + z
                                         -- and not (x + y) + z = x + (y + z)

    -- the same example, proved in yet another way:
    example (x y : ℕ) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
      calc (x + y) * (x + y) = (x + y) * x + (x + y) * y     : by rw mul_add
                         ... = x * x + y * x + x * y + y * y : by rw [add_mul,add_mul,←add_assoc]

    -- the same example, proved in still another way:
    example (x y : ℕ) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
      calc (x + y) * (x + y) = x * x + y * x + x * y + y * y : by simp [add_mul,mul_add]

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

  /- We can view `exists.intro` as an information-hiding operation, since it hides 
     the witness to the body of the assertion. 

     The existential elimination rule, `exists.elim`, performs the opposite operation. 
     It allows us to prove a proposition `q` from `∃ x : α, p x`, by showing that `q` follows 
     from `p w` for an arbitrary value `w`. 

     Roughly speaking, since we know there is some `x` satisfying `p x`, we can give it a name, 
     say, `w`. If `q` does not mention `w`, then showing that `q` follows from `p w` is tantamount 
     to showing that `q` follows from the existence of any such `x`.  -/

  namespace example3
    variables (α : Type) (p q : α → Prop)

    example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
      exists.elim h
      (assume w,
        assume hw : p w ∧ q w,
        show ∃ x, q x ∧ p x, from ⟨w, hw.right, hw.left⟩)

    /- IMPORTANT NOTE: 
       The anonymous constructor notation ⟨w, hw.right, hw.left⟩ abbreviates a nested application.
       Equivalently, ⟨w, ⟨hw.right, hw.left⟩⟩. -/

  end example3

  /- It may be helpful to compare the exists-elimination rule to the or-elimination rule: 
     the assertion ∃ x : α, p x can be thought of as a big disjunction of the propositions p a, 
     as a ranges over all the elements of α. -/

  /- An existential proposition is very similar to a sigma type (Sec 2.8). The difference is that, given 
     `a : α` and `h : p a`, the term 
                                      `exists.intro a h` has type  `(∃ x : α, p x) : Prop` 
     whereas the term 
                                      `sigma.mk a h`     has type  `(Σ x : α, p x) : Type`  
     The similarity between ∃ and Σ is another instance of Curry-Howard. -/

  -- PATTERN MATCHING --
  namespace example4
    variables (α : Type) (p q : α → Prop)
    
    example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
      match h with ⟨w, hw⟩ :=  
        ⟨w, hw.right, hw.left⟩ 
      end
  
    -- We can (and should, imho) annotate the types used in the match for greater clarity.
    example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
      match h with ⟨(w: α), (hw : p w ∧ q w)⟩ :=  
      ⟨w, hw.right, hw.left⟩ 
      end

    -- We can even use match to decompose the conjunction at the same time.
    example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
      match h with ⟨(w: α), (hwp : p w), (hwq : q w)⟩ := ⟨w, hwq, hwp⟩ end

    -- Lean will even allow us to use an implicit match in the assume statement:
    example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
      assume ⟨(w: α), (hwp : p w), (hwq : q w)⟩, ⟨w, hwq, hwp⟩

    -- In Ch 8 we see that all these variations are instances of a more general pattern-matching construct.

  end example4

  /- Next, we define `even a` as `∃ b, a = 2*b`, and then show the sum of two even numbers is even. -/
  namespace example5
    def is_even (a : ℕ) := ∃ b, a = 2 * b

    theorem even_plus_even_is_even {a b : ℕ}
      (h₁ : is_even a) (h₂ : is_even b) : is_even (a + b) :=
      exists.elim h₁ 
        (assume w₁, assume hw1 : a = 2 * w₁,
          exists.elim h₂
            (assume w₂, assume hw2 : b = 2 * w₂,
              exists.intro (w₁ + w₂)
                (calc
                  a + b = 2 * w₁ + 2 * w₂ : by rw [hw1, hw2]
                    ... = 2 * (w₁ + w₂)   : by rw mul_add)))

    -- we can rewrite the last proof more concisely...
    theorem even_plus_even {a b : ℕ}
      (h₁ : is_even a) (h₂ : is_even b) : is_even (a + b) :=
    match h₁, h₂ with
      ⟨w₁, hw1⟩, ⟨w₂, hw2⟩ := ⟨w₁ + w₂, by rw [hw1, hw2, mul_add]⟩
    end

    -- ...again, it's clearer to annotate the types.
    theorem even_plus_even' {a b : ℕ}
      (h₁ : is_even a) (h₂ : is_even b) : is_even (a + b) :=
    match h₁, h₂ with
      ⟨(w₁ : ℕ), (hw1: a = 2 * w₁)⟩, ⟨(w₂ : ℕ), (hw2 : b = 2 * w₂)⟩ := 
      ⟨w₁ + w₂, by rw [hw1, hw2, mul_add]⟩
    end
  end example5  

  /- Just as the constructive "or" is stronger than the classical "or," 
     so, too, is the constructive "exists" stronger than the classical "exists". 
     For example, the following implication requires classical reasoning because, 
     from a constructive standpoint, knowing that it is not the case that every x 
     satisfies `¬ p x` is not the same as having a particular `x` that satisfies `p x`.
  -/   

  namespace example6
    open classical
    variables (α : Type) (p : α → Prop)
    example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
      by_contradiction
        (assume h₁ : ¬ ∃ x, p x,
          have h₂ : ∀ x, ¬ p x, from
            assume x,
            assume h₃ : p x,
            have h₄ : ∃ x, p x, from ⟨x, h₃⟩,
            show false, from h₁ h₄,
          show false, from h h₂)
  end example6

  /- Here are some common identities involving the existential quantifier. (Prove as many as you can and
     determine which are nonconstructive, and hence require some form of classical reasoning.) -/

  namespace constructive_examples

  variables (α :Type) (p q : α → Prop)
  variable a : α
  variable r : Prop

  example : (∃ x : α, r) → r := assume ⟨(w : α), hr⟩, hr
  example : r → (∃ x : α, r) := exists.intro a
  example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := iff.intro
    -- ⇒ 
    (assume ⟨w, (h₁ : p w ∧ r)⟩, ⟨⟨w, h₁.left⟩, h₁.right⟩)   
    -- ⇐
    (assume (h : (∃ x, p x) ∧ r),
      exists.elim h.left 
      (assume w, 
        assume hpw : p w,
         show (∃ x, p x ∧ r), from ⟨w, hpw, h.right⟩
      )        
    )

  example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := iff.intro
    -- ⇒ 
    (assume ⟨w, (h₁ : p w ∨ q w)⟩, 
      or.elim h₁
        (assume hpw : p w, or.inl ⟨w, hpw⟩)
        (assume hqw : q w, or.inr ⟨w, hqw⟩))
    -- ⇐
    (assume h : (∃ x, p x) ∨ (∃ x, q x),
      or.elim h
        (assume ⟨w, hpw⟩, ⟨w, or.inl hpw⟩)
        (assume ⟨w, hpq⟩, ⟨w, or.inr hpq⟩))

  end constructive_examples



  namespace example1
  /-  (∀ x, p x) ↔ ¬ (∃ x, ¬ p x)

      NOTE: for this example, only one direction require classical axioms.
      We split the proof up in two in order to highlight this fact. -/

    variables (α :Type) (p q : α → Prop)
    variable a : α
    variable r : Prop

  -- Constructive direction:
    theorem constructive₁ : (∀ x, p x) → ¬ (∃ x, ¬ p x) := 
      assume h : ∀ x, p x,
      assume h' : (∃ x, ¬ p x),  -- then reach a contradiction, to conclude `¬ (∃ x, ¬ p x)`
        exists.elim h'
          (assume w, 
            assume hw': ¬ p w, 
            have hw : p w, from h w,
            show false, from hw' hw)

  -- Classical direction:

    open classical    

    lemma dne : Π {α : Type} {x : α} {p : α → Prop}, (¬ ¬ (p x)) → (p x) := 
      λ (α : Type) (x : α) (p : α → Prop) (h : ¬ ¬ p x), 
        or.elim (em (p x))
        (assume h₂ : p x, h₂)  -- alternatively,  (assume h₂ : ¬p, absurd h₂ h)
        (assume h₃ : ¬ p x, false.elim (h h₃))

    #check dne

    theorem classical₁ : ¬ (∃ x, ¬ p x) → (∀ x, p x) :=
      assume h₁ : ¬ (∃ x, ¬ p x), 
      by_contradiction
        (assume hc : ¬ (∀ x, p x), -- (reach a contradiction to prove `∀ x, p x`)
         have hcc : ∀ x, ¬ ¬ p x, from
           assume w,
           assume h₂ : ¬ p w, -- (reach a contradiction to prove hcc)
           have h₃ : ∃ x, ¬ p x, from ⟨w, h₂⟩,
           show false, from h₁ h₃, -- (done proving hcc)
         have hz : ∀ x, p x, from
           assume z,
           show p z, from dne (hcc z),
         show false, from hc hz)

    #check classical₁

  end example1



  namespace example2
  /- We are asked to prove the following equivalence:  
       (∃ x, p x) ↔ ¬ (∀ x, ¬ p x)
     As above, we split it up to show one direction can be done constructively. -/

    variables (α :Type) (p q : α → Prop)
    variable a : α
    variable r : Prop

    theorem constructive₂ : (∃ x, p x) → ¬ (∀ x, ¬ p x) := 
      assume h : ∃ x, p x,
      assume h' : ∀ x, ¬ p x,  -- reach a contradiction (this is how we prove a negation)
      exists.elim h 
        (assume w,
        assume hc : p w,
        have hnc : ¬ p w, from h' w,
        show false, from hnc hc)

    #check constructive₂


    open classical

    theorem classical₂ : ¬ (∀ x, ¬ p x) → (∃ x, p x) := 
      assume h : ¬ (∀ x, ¬ p x),
        by_contradiction (
          assume h₁ : ¬ (∃ x, p x),  -- (reach a contradiction to prove `∃ x, p x`) 
            have hcc : ∀ x, ¬ p x, from
            assume w,
            assume h₂ : p w, -- (reach a contradiction to prove hcc)
            have h₃ : ∃ x, p x, from ⟨w, h₂⟩,
            show false, from h₁ h₃, -- (done proving hcc)
          show false, from h hcc)


  end example2

  namespace example3
  /- We are asked to prove the following equivalence:  
       (¬ ∃ x, p x) ↔ (∀ x, ¬ p x)
     Again, we split it up to show one direction can be done without classical axioms. -/

    variables (α :Type) (p q : α → Prop)
    variable a : α
    variable r : Prop

    theorem constructive₃ : (∀ x, ¬ p x) → (¬ ∃ x, p x) :=
      assume h : ∀ x, ¬ p x,
      assume hn : ∃ x, p x,
        exists.elim hn (
          assume w,
          assume hw : p w,
          have hwc : ¬ p w, from h w,
          show false, from hwc hw)
      
  
    open classical
    theorem classical₃ : (¬ ∃ x, p x) → (∀ x, ¬ p x) := 
      assume h : ¬ ∃ x, p x,
      by_contradiction (
        assume hc : ¬ (∀ x, ¬ p x),
        have hcc : ∃ x, p x, from 
          example2.classical₂ α p hc,
        show false, from h hcc)

  end example3
  

  namespace example4
  /- `(¬ ∀ x, p x) ↔ (∃ x, ¬ p x)` splits into constructive/classical directions -/
    variables (α :Type) (p q : α → Prop)
    variable a : α
    variable r : Prop
    theorem constructive₄ : (∃ x, ¬ p x) → (¬ ∀ x, p x) := 
      assume h : ∃ x, ¬ p x,
      assume hn : ∀ x, p x,
        exists.elim h 
          (assume w,
            assume hnw : ¬ p w,
            have hw : p w, from hn w,
            show false, from hnw hw)

    open classical
    theorem classical₄ : (¬ ∀ x, p x) → (∃ x, ¬ p x) := 
      assume h : ¬ ∀ x, p x,
      by_contradiction (
        assume hn : ¬ (∃ x, ¬ p x),
        have hc : ∀ x, p x, from example1.classical₁ α p hn,        
        show false, from h hc)

   end example4
    

  namespace example5
  /- (∀ x, p x → r) ↔ (∃ x, p x) → r
     In this case, neither direction requires classical axioms. -/

    variables (α :Type) (p q : α → Prop)
    variable a : α
    variable r : Prop

    theorem constructive₅ : (∀ x, (p x → r)) ↔ (∃ x, p x) → r := iff.intro

      (assume h₁ : ∀ x, (p x → r),
        assume h₂ : ∃ x, p x,
        exists.elim h₂
          (assume w,
            assume hw : p w,
            show r, from h₁ w hw))

      (assume h : ((∃ x, p x) → r),
        assume w,
        assume hw : p w,
        show r, from h ⟨w, hw⟩)
  end example5


  namespace example6
  /- (∃ x, p x → r) ↔ (∀ x, p x) → r := -/
    variables (α :Type) (p q : α → Prop)
    variable a : α
    variables r s t: Prop

    theorem constructive₆ : (∃ x, p x → r) → (∀ x, p x) → r := 
    -- N.B. this theorem says  (∃ x, (p x → r)) → ((∀ x, p x) → r)
      (assume h : ∃ x, p x → r,
        assume h' : ∀ x, p x,
        exists.elim h
          ( assume w,
            assume hw : p w → r,
            show r, from hw (h' w) )
      )
    theorem constructive₉ : (∀ x, p x) → r → (∃ x, p x → r) :=  
    -- N.B. this theorem says  ((∀ x, p x) →  r) → (∃ x, (p x → r))
     assume (h₁ : ∀ x, p x) (h₂ : r),
       have hrpar: r → (p a → r), from
         assume (hr: r) (hpa: p a), hr,
       have hpar : p a → r, from hrpar h₂,
       exists.intro a hpar

   open classical
   theorem classical₆ : ((∀ x, p x) → r) → (∃ x, p x → r) := sorry
   -- -- N.B. this theorem says  (∀ x, p x) → ( r → (∃ x, (p x → r)) )
                                       
  end example6

  namespace example7
    variables (α :Type) (p q : α → Prop)
    variable a : α
    variables r s t: Prop
    example : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
  end example7  
    

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

