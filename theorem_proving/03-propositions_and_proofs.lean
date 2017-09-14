-- Chapter 3. Propositions and Proofs

/- This chapter explains how to write mathematical assertions and proofs in the language
of dependent type theory. -/

#print "=================================="
#print "Section 3.1 Propositions as Types"
#print " "

namespace Sec_3_1
  /- We introduce a new type, `Prop`, to represent propositions, and introduce 
     constructors to build new propositions from others.
  -/
  constant and : Prop → Prop → Prop
  constant or : Prop → Prop → Prop
  constant not : Prop → Prop
  constant implies : Prop → Prop → Prop

  variables p q r : Prop
  #check and p q                      -- Prop
  #check or (and p q) r               -- Prop
  #check implies (and p q) (and q p)  -- Prop


  /- We then introduce, for each `p : Prop`, another type `Proof p`, for the type 
     of proofs of `p`. An "axiom" would be constant of such a type. -/
  constant Proof : Prop → Type

  -- example of an axiom:
  constant and_comm : Π (p q : Prop), Proof (implies (and p q) (and q p))

  #check and_comm p q      -- Proof (implies (and p q) (and q p))
  
  /- In addition to axioms, however, we would also need rules to build new proofs from 
     old ones. For example, in many proof systems for propositional logic, we have the 
     rule of modus ponens. -/
  constant modus_ponens (p q : Prop) : Proof (implies p q) →  Proof p → Proof q
  constant modus_ponens' : Π (p q : Prop), Proof (implies p q) →  Proof p → Proof q
  #check modus_ponens p q
  #check modus_ponens' p q
 
  /- Systems of natural deduction for propositional logic also typically rely on 
     the following rule: -/

  constant implies_intro (p q : Prop) : (Proof p → Proof q) → Proof (implies p q).

  /- This approach would provide us with a reasonable way of building assertions and proofs. 
     Determining that an expression =t= is a correct proof of assertion =p= would then 
     simply be a matter of checking that =t= has type =Proof p=. -/

  /- Some simplifications are possible. We can avoid writing the term =Proof= repeatedly 
     by conflating =Proof p= with =p= itself. Whenever we have =p : Prop=, we can interpret
     =p= as a type, namely, the type of its proofs. -/

  /- We read =t : p= as the assertion that =t= is a proof of =p=. -/

  /- The rules for implication then show that we can identify =implies p q= and =p → q=.  -/

  /- In other words, implication =p → q= corresponds to existence of a function taking 
     elements of =p= to elements of =q=. Thus the introduction of the connective =implies= 
     is redundant: we can use the usual function space constructor =p → q= from dependent 
     type theory as our notion of implication. -/

  /- The rules for implication in a system of natural deduction correspond to the rules 
     governing abstraction and application for functions. This is an instance of the 
     /Curry-Howard correspondence/, or /propositions-as-types/ paradigm. -/

  /- In fact, the type =Prop= is syntactic sugar for =Sort 0=, the very bottom of the type 
     hierarchy.  Moreover, =Type u= is also just syntactic sugar for =Sort (u+1)=. -/

  /- =Prop= has some special features, but like the other type universes, it is closed 
     under the arrow constructor: if =p q : Prop=, then =p → q : Prop=. -/

  /- There are at least two ways of thinking about propositions-as-types (pat).  

     Constructive view: pat is a faithful rendering of what it means to be a proposition: 
     a proposition `p` is a data type that represents a specification of the type of 
     data that constitutes a proof.  A proof `t` of `p` is simply an object of type `p`,
     denoted `t : p`. 

     Non-constructive view: pat is a simple coding trick. To each proposition `p` we 
     associate a type, which is empty if `p` is false and has a *single* element, 
     say `*`, if `p` is true. In the latter case, we say (the type associated with)
     `p` is *inhabited*. It just so happens that the rules for function application and 
     abstraction can conveniently help us keep track of which elements of `Prop` are 
     inhabited. So constructing an element =t : p= tells us that =p= is indeed true. 
     You can think of the inhabitant of =p= as being "the fact that `p` has a proof." 
     (Lean document says, "the fact that `p` is true" but they're conflating "truth" 
     with "has a proof".)  -/

  /- PROOF IRRELEVANCE: 

     If `p : Prop` is any proposition, Lean's kernel treats any two elements `t1 t2 : p` 
     as being definitionally equal.  This is known as "proof irrelevance," and is 
     consistent with the non-constructive interpretation above. It means that even 
     though we can treat proofs =t : p= as ordinary objects in the language of dependent
     type theory, they carry no information beyond the fact that =p= is true. -/

  /- IMPORTANT DISTINCTION: 

     "proofs as if people matter" or "proof relevance"
     From the constructive point of view, proofs are *abstract mathematical objects* that 
     may be denoted (in various ways) by suitable expressions in dependent type theory. 

     "proofs as if people don't matter" or "proof irrelevance"
     From the non-constructive point of view, proofs are not abstract entities. 
     A syntactic expression---that we formulate using type theory in order to prove 
     a proposition---doesn't denote some abstract proof.  Rather, the expression itself
     /is/ the proof. And such an expression does not denote anything beyond the fact that 
     (assuming it type-checks) the proposition in question is "true" (i.e., has a proof). -/

  /- We may slip back and forth between these two ways of talking, at times saying that 
     an expression "constructs" or "represents" a proof of a proposition, and at other times
     simply saying that it "is" such a proof. 

     This is similar to the way that computer scientists occasionally blur the distinction 
     between syntax and semantics by saying, at times, that a program "computes" a certain 
     function, and at other times speaking as though the program "is" the function in question.
  -/

  /- In any case, all that really matters is that the bottom line is clear. To formally express
     a mathematical assertion in the language of dependent type theory, we need to exhibit a 
     term =p : Prop=. To /prove/ that assertion, we need to exhibit a term =t : p=. Lean's
     task, as a proof assistant, is to help us to construct such a term, =t=, and to verify 
     that it is well-formed and has the correct type.
  -/


  #print " "
end Sec_3_1

/- Section 3.1 output:
                and p q : Prop
                or (and p q) r : Prop
                implies (and p q) (and q p) : Prop
                and_comm p q : Proof (implies (and p q) (and q p))
-/

#print "================================================"
#print "Section 3.2 Working with Propositions as Types"
#print " "

namespace page34
  #print "-------------- page 34 ----------------"

  constants p q : Prop

  theorem t1 : p → q → p := λ hp : p, λ hq : q, hp

  theorem t1' : p → q → p :=
  assume hp : p,
  assume hq : q,
  hp
  #print t1'   -- page34.t1' : p → q → p := λ (hp : p) (hq : q), hp

  lemma t1'' : p → q → p := assume hp : p, assume hq : q, show p, 
    from hp

  #print " "
end page34



namespace page35
  #print "-------------- page 35 ----------------"

  constants p q : Prop

  /- As with ordinary defs, we can move lambda-abstracted variables to the left of colon. -/
  theorem t1 (hp : p) (hq : q) : p := hp
  #check t1   -- p → q → p

  /- Now we can apply the theorem t1 just as a function application. -/

  axiom hp : p     -- alternative syntax for `constant hp : p`
  theorem t2 : q → p := t1 hp

  theorem gen_t1 (p q : Prop) (Hp : p) (hp : q) : p := Hp
  #check gen_t1                                             -- (p q : Prop), p → q → p

  -- or we can move some parameters to the right of the colon
  theorem gen_t1' (p q : Prop) : p → q → p := λ (Hp : p) (hp : q), Hp
  #check gen_t1'

  -- or we can move all parameters to the right of the colon
  theorem gen_t1'' : Π (p q : Prop), p → q → p := λ (p q : Prop) (Hp : p) (hp : q), Hp
  #check gen_t1''

  -- but gen_t1, gen_t1', gen_t1'' all have same type, namely, `(p q : Prop), p → q → p`

  /- The symbol ∀ is alternate syntax for Π.  Later we see how Pi types model universal 
     quantifiers more generally.  For the moment, however, we focus on theorems in logic, 
     generalized over propositions. We will tend to work in sections with variables over 
     propositions, so that they are generalized for us automatically. 
     When we generalize t1 in that way, we can then apply it to different pairs of 
     propositionshe to obtain different instances of the general theorem. -/
  #print " "
end page35

namespace page36 -- (page 26 of new edition)

  #print "-------------- page 36 ----------------"

  variables p q r s : Prop
  variable h : r → s
  #check h
  #check r → s

  theorem t1 : Π (p q : Prop), p → q → p := λ (p q : Prop) (Hp : p) (hp : q), Hp

  #check t1 p q
  #check t1 r s
  #check t1 (r → s) (s → r)
  #check t1 (r → s) (s → r) h

  theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r := λ (x : p), h₁ (h₂ x)

  theorem t2' : Π (h₁ : q → r) (h₂ : p → q), p → r := 
    λ (h₁ : q → r) (h₂ : p → q) (x : p), h₁ (h₂ x)

  theorem t2'' (h₁ : q → r) (h₂ : p → q): p → r := 
  assume h₃ : p,                                          -- like Coq's `intro` tactic
  show r, from h₁ (h₂ h₃)

  /- As a theorem of propositional logic, what does thm2 say? 
     (given `p implies q` and `q implies r`, we can derive `p implies r`) -/
  #print " "

end page36

/- Section 3.2 output:
                theorem page34.t1' : p → q → p :=
                λ (hp : p) (hq : q), hp
                t1 : p → q → p
                gen_t1 : ∀ (p q : Prop), p → q → p
                gen_t1' : ∀ (p q : Prop), p → q → p
                gen_t1'' : ∀ (p q : Prop), p → q → p
                h : r → s
                r → s : Prop
                t1 p q : p → q → p
                t1 r s : r → s → r
                t1 (r → s) (s → r) : (r → s) → (s → r) → r → s
                t1 (r → s) (s → r) h : (s → r) → r → s
-/



#print "================================="
#print "Section 3.3 Propositional Logic"
  #print " "
/- Propositional connectives are operators on the space Prop 
   For example, if we have p q r : Prop, then the expression
   p → q  read "if p then q" and this is a Prop, so we see
   that → is a binary operation on Prop; thus we could write
   → : Prop × Prop → Prop

   the expression p → q → r reads 
   "if p, then if q, then r." NB this is the "curried" form of p ∧ q → r. -/

/- Lambda abstraction can be viewed as an "introduction rule" for →. 
   It "introduces" (or establishes) an implication.  

   Application, on the other hand, is an "elimination rule" for →.
   It shows how to "eliminate" or /use/ an implication in a proof. -/ 


-- ____CONJUNCTION____

namespace page37
  #print "-------------- page 37 ----------------"

  /- The expression and.intro h1 h2 builds a proof of p ∧ q using proofs h1 : p and h2 : q. 
     `and.intro` is known as the "and-introduction rule." -/

  -- __AND_INTRO__

  -- Let's use `and.intro` to create a proof of `p → q → p ∧ q`.
  variables p q : Prop
  theorem t3 (hp : p) (hq : q) :  p ∧ q := and.intro hp hq
  #check t3

  -- Alternatively, 
  theorem t3' : Π (hp : p) (hq : q),  p ∧ q := λ (h₁ : p) (h₂ :q), and.intro h₁ h₂
  #check t3'


  -- __AND_ELIM__

  /- `and.elim_left` gives a proof of `p` from a proof of `p ∧ q`.   
     Similarly for `and.elim_right` and `q`, resp. 
     These are known as the right and left /and-elimination/ rules. -/
  example (h : p ∧ q) : p := and.elim_left h   -- std lib abbreviation: `and.left`
  example (h : p ∧ q) : q := and.elim_right h  -- std lib abbreviation: `and.right`

  /- The `example` command states a theorem without naming it or storing it in the 
     permanent context. It just checks that the given term has the indicated type. -/

  -- Let's prove `p ∧ q → q ∧ p`
  theorem and_comm (h : p ∧ q) : q ∧ p := and.intro (and.right h) (and.left h)
  #check and_comm

  theorem and_comm' : Π (α : Prop) (β : Prop), (α ∧ β) → (β ∧ α) := 
          λ (α β : Prop), λ (h : α ∧ β), and.intro (and.right h) (and.left h)
  #check and_comm'

  #print " "
end page37

/- `and-introduction` and `and-elimination` are similar to the pairing and projection 
   operations for the cartesian product. The difference is that given `hp : p` and `hq : q`, 
   `and.intro hp hq` has type `p ∧ q : Prop`, while `pair hp hq` has type `p × q : Type`.

   The similarity between ∧ and × is another instance of the Curry-Howard isomorphism, but
   in contrast to implication and the function space constructor, ∧ and × are treated sepa-
   rately in Lean.
-/


namespace page38
  #print "-------------- page 38 ----------------"

  -- __ANONYMOUS_CONSTRUCTORS__

  /- Certain types in Lean are structures, which is to say, the type is defined with a 
     single canonical constructor which builds an element of the type from a sequence of 
     suitable arguments. The expression `p ∧ q` is an example. -/

  /- Lean allows us to use *anonymous constructor* notation ⟨arg1, arg2, ...⟩ in situations 
     like these, when the relevant type is an inductive type and can be inferred from the 
     context. In particular, we can often write ⟨hp, hq⟩ instead of and.intro hp hq. -/

  variables p q : Prop
  variables (hp : p) (hq : q)

  #check (⟨hp, hq⟩ : p ∧ q)        -- and.intro hp hq : p ∧ q

  /- Here's another useful syntactic gadget. Given an expression `e` of an inductive 
     type `fu`, the notation e.bar is shorthand for `fu.bar e`. Thus we can access 
     functions without opening a namespace. For example, these mean the same thing. -/
  variable l : list ℕ
  #check list.head l               -- list.head l : ℕ
  #check l.head                    -- list.head l : ℕ

  /- Another example: given `h : p ∧ q`, we can write `h.left` for `and.left h` and 
     `h.right` for `and.right h`.  Thus the sample proof above can be given as follows: -/
  example (h : p ∧ q) : q ∧ p := ⟨h.right, h.left⟩

  #print " "
end page38

/-  ____DISJUNCTION____

   `or.intro_left q hp` creates a proof of `p ∨ q` from a proof `hp : p`.
   `or.intro_right p hq` creates a proof of `p ∨ q` from a proof `hq : q`. 
   These are called the left and right "or-introduction" rules. 
-/

namespace page39a
  #print "-------------- page 39 ----------------"

  -- __OR_INTRO__

  variables p q : Prop
  example (h₁ : p) : p ∨ q := or.intro_left q h₁
  example (h₂ : q) : p ∨ q := or.intro_right p h₂

  -- __OR_ELIM__

  /- The `or-elimination` rule is slightly more complicated. The idea is that we can prove
     `r` from `p ∨ q`, by showing that `r` follows from `p` and that `r` follows from `q`.  -/

  /- In the expression `or.elim hpq hpr hqr`, the function `or.elim` takes three arguments:
            hpq : p ∨ q,     hpr : p → r,     hqr : q → r
     and produces a proof of `r`. 
  -/

end page39a

namespace page39b
  -- Let's use `or.elim` to prove `p ∨ q → q ∨ p`.
  theorem or_comm₁ : Π (p q : Prop), p ∨ q → q ∨ p := λ (p q : Prop) (h : p ∨ q), 
      or.elim h (λ (h₁ : p), or.intro_right q h₁) (λ (h₂ : q), or.intro_left p h₂)
  -- note that using a Π type, we don't need to introduce variables p and q in advance

  -- Here's the tutorial's version 
  -- (note we need to introduce p and q as variables)

  variables p q : Prop
  example (h : p ∨ q) : q ∨ p :=
    or.elim h
      (assume h₁ : p,
        show q ∨ p, from or.intro_right q h₁)
      (assume h₂ : q,
        show q ∨ p, from or.intro_left p h₂)

  -- Here's an alternative version from the tutorial.
  theorem or_comm₂ (h : p ∨ q) : q ∨ p := 
    or.elim h (λ (h₁ : p), or.inr h₁) (λ (h₂ : q), or.inl h₂)

  #check or_comm₁
  #check or_comm₂
  #print " "
end page39b

/-In most cases, the first argument of or.intro_right and or.intro_left can be in-
ferred automatically by Lean. Lean therefore provides or.inr and or.inl as shorthands
for or.intro_right _ and or.intro_left _. Thus the proof term above could be written
more concisely: -/

namespace page40
  #print "-------------- page 40 ----------------"

  variables p q r : Prop
  -- variables (h₁ : p) (h₂ : q)

  /- Because or has two constructors, we cannot use anonymous constructor notation. 
     But we can still write h.elim instead of or.elim h. -/
  theorem or_comm (h : p ∨ q) : q ∨ p := 
    h.elim (λ (h₁ : p), or.inr h₁) (λ (h₂ : q), or.inl h₂)
  
  #check or_comm

  -- Negation and Falsity
  /- Negation, `¬p`, is defined to be p → false, so we obtain ¬p by assuming
     p and then deriving a contradiction. 

     Similarly, the expression `hnp hp` produces a proof of false from `hp : p`
     and `hnp : ¬p`. The next example uses both these rules to produce a proof of 
     `(p → q) → ¬q → ¬p`.
  -/
  theorem mt (hpq : p → q) (hnq : ¬q) : ¬p :=
    assume hp : p,
    show false, from hnq (hpq hp)

  #check mt

  -- Alternatively, without predeclared variables,
  theorem mt₁ : Π (p q : Prop),  (p → q) → ¬q → ¬p := 
    λ (p q : Prop) (h₁: p → q) (h₂ : ¬q) (h₃ : p), h₂ (h₁ h₃) 
  #print mt₁
  /- The connective false has a single elimination rule, false.elim, which 
     expresses the fact that anything follows from a contradiction. This 
     rule is sometimes called ex falso, or the principle of explosion. -/

  example (h₁ : p) (h₂ : ¬p) : q := false.elim (h₂ h₁)
  example (h₁ : p) (h₂ : ¬p) : q := absurd h₁ h₂ -- notice reversal of order of hypoths
  example (h₁ : ¬p) (h₂ : q) (h₃ : q → p) : r := absurd (h₃ h₂) h₁

  /- Alternatively, without predeclared variables, the last three examples could 
     be implemented using Π types and λ terms.   -/
  theorem ex_falso₁ : Π (p q : Prop), p → ¬p → q := 
    λ (p q : Prop) (h₁ : p) (h₂ : ¬p), false.elim (h₂ h₁)

  theorem ex_falso₂ : Π (p q : Prop), p → ¬p → q := 
    λ (p q : Prop) (h₁ : p) (h₂ : ¬p), absurd h₁ h₂

  theorem absurd_example : Π (p q r : Prop), ¬p → q → (q → p) → r :=
    λ (p q r : Prop) (h₁ : ¬p) (h₂ : q) (h₃ : q → p), absurd (h₃ h₂) h₁

  #print " "
end page40


namespace page41
  #print "-------------- page 41 ----------------"

  /- __Logical Equivalence__
    The expression `iff.intro h1 h2` produces a proof of `p ↔ q` from `h1 : p → q` and 
    `h2 : q → p`. The expression `iff.elim_left h` produces a proof of `p → q` from 
    `h : p ↔ q`. Similarly, `iff.elim_right h` produces a proof of `q → p` from 
    `h : p ↔ q`. -/
  variables p q r : Prop
  variables (hp : p) (hq : q)

  theorem and_swap : p ∧ q ↔ q ∧ p :=
    iff.intro
      (assume h: p ∧ q,
        show q ∧ p, from and.intro (and.elim_right h) (and.elim_left h))
      (assume h: q ∧ p,
        show p ∧ q, from and.intro (and.elim_right h) (and.elim_left h))

  theorem and_swap₁ : p ∧ q ↔ q ∧ p :=
    iff.intro
      (assume h: p ∧ q, show q ∧ p, from and.intro h.right h.left)
      (assume h: q ∧ p, show p ∧ q, from and.intro h.right h.left)

  theorem and_swap₂ : p ∧ q ↔ q ∧ p :=
    iff.intro  (λ (h: p ∧ q), and.intro h.right h.left)
      (λ (h: q ∧ p), and.intro h.right h.left)

  theorem and_swap₃ : Π (p q : Prop), p ∧ q ↔ q ∧ p := λ (p q : Prop), 
    ⟨(λ (h₁: p ∧ q), ⟨h₁.right, h₁.left⟩), (λ (h₂: q ∧ p), ⟨h₂.right, h₂.left⟩)⟩


  theorem and_swap₄ : Π (p q : Prop), p ∧ q ↔ q ∧ p := λ (p q : Prop), 
    iff.intro 
      (λ (h₁: p ∧ q), ⟨h₁.right, h₁.left⟩) 
      (λ (h₂: q ∧ p), ⟨h₂.right, h₂.left⟩)


  #check and_swap                        -- ∀ (p q : Prop), p ∧ q ↔ q ∧ p
  #check and_swap₁                        -- ∀ (p q : Prop), p ∧ q ↔ q ∧ p
  #print "--"
  #check and_swap p                      --   ∀ (q : Prop), p ∧ q ↔ q ∧ p
  #check and_swap₂ p                      --   ∀ (q : Prop), p ∧ q ↔ q ∧ p
  #print "--"
  #check and_swap p q                    --                 p ∧ q ↔ q ∧ p
  #check and_swap₃ p q                    --                 p ∧ q ↔ q ∧ p

  /- iff.elim_left and iff.elim_right represent a form of modus ponens,
     so they can be abbreviated iff.mp and iff.mpr, respectively. -/

  /- We can use the anonymous constructor notation to construct a proof of p ↔ q from 
     proofs of the forward and backward directions, and we can also use . notation with 
     mp and mpr. -/

  theorem and_swap₅ : p ∧ q ↔ q ∧ p :=
    ⟨λ (h : p ∧ q), ⟨h.right, h.left⟩, λ (h : q ∧ p), ⟨h.right, h.left⟩⟩

  example (h : p ∧ q) : q ∧ p := (and_swap₅ p q).elim_left h

  example (h : p ∧ q) : q ∧ p := (and_swap₅ p q).mp h

  #print " "
end page41


#print "  "
#print "==========================================="
#print "Section 3.4 Introducing Auxiliary Subgoals"
#print "  "
  /- This is a good place to introduce another device Lean offers to help 
     structure long proofs, namely, the `have` construct, which introduces 
     an auxiliary subgoal in a proof. -/

namespace Sec_3_4
  variables p q : Prop
  
  theorem and_swap (h : p ∧ q) : q ∧ p :=
    have h₁ : p, from and.elim_left h,
    have h₂ : q, from and.elim_right h,
    show q ∧ p, from  and.intro h₂ h₁

  -- `show` is just for clarity; it's not required, as we see here.
  theorem and_swap₁ (h : p ∧ q) : q ∧ p :=
    have h₁ : p, from and.elim_left h,
    have h₂ : q, from and.elim_right h, and.intro h₂ h₁

  /- Under the hood, the expression 
         have h : p, from s, t
     produces the term 
         (λ (h : p), t) s

     In other words, `s` is a proof of `p`, `t` is a proof of the desired 
     conclusion assuming `h : p`, and the two are combined by lambda 
     astraction and application. -/

  /- Lean also supports a structured way of reasoning backwards from a goal,
     which models the "suffices to show" construction in ordinary mathematics. -/

  theorem and_swap₂ (h : p ∧ q) : q ∧ p :=
    have h₁ : p, from and.elim_left h,
    suffices h₂ : q, from and.intro h₂ h₁,
    show q, from and.elim_right h

  #check and_swap₁
  #check and_swap₂

end Sec_3_4


#print "  "
#print "====================================="
#print "Section 3.5 Classical Logic"
#print "  "

namespace page43

  /- The constructive "or" is very strong: asserting p ∨ q amounts to knowing
     which is the case. If RH represents the Riemann hypothesis, a classical 
     mathematician is willing to assert RH ∨ ¬RH, even though we cannot yet 
     assert either disjunct. -/

  open classical 

  #check λ (p : Prop), em p            -- p ∨ ¬p

  /- One consequence of the law of the excluded middle is the principle of double-negation
     elimination: -/
  theorem dne {p : Prop} (h : ¬¬p) : p :=
    or.elim (em p)
      (assume h₁ : p, h₁)
      (assume h₂ : ¬p, false.elim (h h₂))  -- alternatively,  (assume h₂ : ¬p, absurd h₂ h)

  #check @dne
  /- double-negation elimination allows one to carry out a proof by contradiction, 
     something which is not always possible in constructive logic. -/

end page43

/- Exercise: prove the converse of dne, showing that em can be proved from dne. -/
namespace exer

  variables p q : Prop

/- first try (didn't get this to work)
  theorem em (h : ¬¬p → p) : p ∨ ¬p :=  
    (λ (h₂ : ¬p), or.inr h₂)
    (λ (h₃ : ¬¬p), or.inl (h h₃))
-/
/- second try, by the `cases` tactic (but this only works in classical)
  theorem em (h : ¬¬p → p) : p ∨ ¬p :=  
  by_cases
    (assume h₂ : ¬p, or.inr h₂)
    (assume h₃ : ¬¬p, or.inl (h h₃))
-/
end exer

#print "  "
#print "================================================"
#print "Section 3.6 Examples of Propositional Validities"
#print "  "
/- Lean's standard library contains proofs of many valid statements of propositional 
   logic, all of which you are free to use in proofs of your own. The following list 
   includes a number of common identities. The ones that require classical reasoning 
   are grouped together at the end, while the rest are constructively valid. -/

namespace Section_3_6
variables p q r s : Prop

-- commutativity of ∧
example : p ∧ q ↔ q ∧ p := iff.intro
  (assume h: p ∧ q,
    show q ∧ p, from and.intro (and.elim_right h) (and.elim_left h))
  (assume h: q ∧ p,
    show p ∧ q, from and.intro (and.elim_right h) (and.elim_left h))

-- commutativity of ∨
example : p ∨ q ↔ q ∨ p := iff.intro
  (assume h₁: p ∨ q,
    show q ∨ p, from or.elim h₁ (assume h₂ : p, or.inr h₂) (assume h₃ : q, or.inl h₃))
  (assume h₁: q ∨ p,
    show p ∨ q, from or.elim h₁ (assume h₁ : q, or.inr h₁) (assume h₂ : p, or.inl h₂))

-- associativity of ∧
example: p ∧ (q ∧ r) ↔ (p ∧ q) ∧ r := iff.intro
  (assume h : p ∧ (q ∧ r),
    show (p ∧ q) ∧ r, from and.intro (and.intro h.left h.right.left) h.right.right) 
  (assume h : (p ∧ q) ∧ r,
    show p ∧ (q ∧ r), from and.intro h.left.left (and.intro h.left.right h.right))

-- associativity of ∨
example: p ∨ (q ∨ r) ↔ (p ∨ q) ∨ r := iff.intro
  (assume h : p ∨ (q ∨ r),
    show (p ∨ q) ∨ r, from or.elim h 
      (assume h₁ : p, or.inl (or.inl h₁)) 
      (assume h₂ : q ∨ r, or.elim h₂
        (assume h₃ : q, or.inl (or.inr h₃))
        (assume h₄ : r, or.inr h₄)))
  (assume h : (p ∨ q) ∨ r,
    show p ∨ (q ∨ r), from or.elim h 
      (assume h₁ : (p ∨ q), or.elim h₁
        (assume h₂ : p, or.inl h₂)
        (assume h₂ : q, or.inr (or.inl h₂)))
      (assume h₃ : r, or.inr (or.inr h₃)))



end Section_3_6

#print "  "
#print "==============================="
#print "Section 3.7 Exercises"
#print "  "
namespace Section_3_7

end Section_3_7


