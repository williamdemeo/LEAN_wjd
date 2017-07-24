-- Chapter 3. Propositions and Proofs

/- This chapter explains how to write mathematical assertions and proofs in the language
of dependent type theory. -/

#print "------------------------------------------------"
#print "Section 3.1 Propositions as Types"
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
  constant and_comm : Π p q : Prop, Proof (implies (and p q) (and q p))

  #check and_comm p q      -- Proof (implies (and p q) (and q p))

  
  /- In addition to axioms, however, we would also need rules to build new proofs from 
     old ones. For example, in many proof systems for propositional logic, we have the 
     rule of modus ponens. -/
  constant modus_ponens (p q : Prop) : Proof (implies p q) →  Proof p → Proof q
 
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

     "proofs as if people matter"
     From the constructive point of view, proofs are *abstract mathematical objects* that 
     may be denoted (in various ways) by suitable expressions in dependent type theory. 

     "proofs as if people don't matter"
     From the non-constructive point of view, the proofs are not abstract entities. 
     A syntactic expression---that we formulate using type theory in order to prove 
     a proposition---doesn't denote some abstract proof.  Rather, the expression is itself
     the proof. And such an expression does not denote anything beyond the fact that 
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


end Sec_3_1

/- Section 3.1 output:
                and p q : Prop
                or (and p q) r : Prop
                implies (and p q) (and q p) : Prop
                and_comm p q : Proof (implies (and p q) (and q p))
-/

#print "------------------------------------------------"
#print "Section 3.2 Working with Propositions as Types"

namespace page34
  constants p q : Prop

  theorem t1 : p → q → p := λ hp : p, λ hq : q, hp

  theorem t1' : p → q → p :=
  assume hp : p,
  assume hq : q,
  hp
  #print t1'   -- page34.t1' : p → q → p := λ (hp : p) (hq : q), hp

  lemma t1'' : p → q → p := assume hp : p, assume hq : q, show p, 
    from hp

end page34

namespace page35
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
end page35

namespace page36
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



#print "------------------------------------------------"
#print "Section 3.3 Propositional Logic"

/- If we have p q r : Prop, the expression p → q → r reads 
   "if p, then if q, then r." NB this is the "curried" form of p ∧ q → r. -/

/- Lambda abstraction can be viewed as an "introduction rule" for →. 
   It "introduces" (or establishes) an implication.  Application, on the other hand,
   is an "elimination rule" showing how to "eliminate" (or use) an implication in a proof. -/ 


namespace page37
  -- Conjunction
  /- The expression and.intro h1 h2 builds a proof of p ∧ q using proofs h1 : p and h2 : q. 
     `and.intro` is known as the "and-introduction rule." -/

  -- Let's use `and.intro` to create a proof of `p → q → p ∧ q`.
  variables p q : Prop
  theorem t3 (hp : p) (hq : q) :  p ∧ q := and.intro hp hq
  #check t3

  -- Alternatively, 
  theorem t3' : Π (hp : p) (hq : q),  p ∧ q := λ (h₁ : p) (h₂ :q), and.intro h₁ h₂
  #check t3'

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
end page37

/- `and-introduction` and `and-elimination` are similar to the pairing and projection 
   operations for the cartesian product. The difference is that given `hp : p` and `hq : q`, 
   `and.intro hp hq` has type `p ∧ q : Prop`, while `pair hp hq` has type `p × q : Type`.

   The similarity between ∧ and × is another instance of the Curry-Howard isomorphism, but
   in contrast to implication and the function space constructor, ∧ and × are treated sepa-
   rately in Lean.
-/

