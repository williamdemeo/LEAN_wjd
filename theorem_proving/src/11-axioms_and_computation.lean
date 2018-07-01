#print "
Chapter 11. Axioms and Computation
==================================

We have seen that the version of the Calculus of Constructions implemented in Lean 
includes 

+ dependent function types, 
+ inductive types, and 
+ a hierarchy of universes that starts with an impredicative, proof-irrelevant `Prop` 
  at the bottom. 
  
We now consider ways of extending the CIC with additional axioms and rules. 
Extending a foundational system is often convenient; it can make it possible 
to prove more theorems, and make it easier to prove theorems that could have been 
proved without extending. 

But there can be negative consequences of adding axioms. Besides concerns about their 
correctness, the use of axioms bears on the computational content of definitions and 
theorems in ways we explore now.

Lean is designed to support both computational and classical reasoning. Users that are 
so inclined can stick to a 'computationally pure' fragment, which guarantees that closed 
expressions in the system evaluate to canonical normal forms. In particular, any closed 
computationally pure expression of type `ℕ`, for example, will reduce to a numeral.

Lean's stdlib defines an additional axiom, propositional extensionality, and a quotient 
construction which in turn implies the principle of function extensionality. These 
extensions are used, for example, to develop theories of sets and finite sets. We will 
see below that using these theorems can block evaluation in Lean's kernel, so that closed 
terms of type `ℕ` no longer evaluate to numerals. But Lean erases types and propositional 
information when compiling definitions to bytecode for its virtual machine evaluator, 
and since these axioms only add new propositions, they are compatible with that 
computational interpretation. Even computationally inclined users may wish to use the 
classical law of the excluded middle to reason about computation. This also blocks 
evaluation in the kernel, but it is compatible with compilation to bytecode.

The stdlib defines a choice principle that is at odds with a computational interpretation, 
since it magically produces 'data' from a proposition asserting the existence of that data.
Its use is essential to some classical constructions, and users can import it when needed. 
But expressions that use this construction to produce data do not have computational content, 
and in Lean we are required to mark such definitions as `noncomputable` to flag that fact.

Using Diaconescu's theorem, we can use propositional extensionality, function extensionality, 
and choice to derive the law of the excluded middle. As noted above, however, use of the 
law of the excluded middle is still compatible with bytecode compilation and code 
extraction, as are other classical principles, *as long as they are not used to manufacture 
data*.

To summarize, then, on top of the underlying framework of universes, dependent function 
types, and inductive types, the standard library adds three additional components:

1. the axiom of propositional extensionality
2. a quotient construction that implies function extensionality
3. a choice principle that produces data from an existential proposition.

The first two of these block normalization within Lean, but are compatible with bytecode 
evaluation, whereas the third is not amenable to computational interpretation. We will 
spell out the details more precisely below."


#print "
Section 11.1. Historical and Philosophical Context
--------------------------------------------------

For most of its history, mathematics was essentially computational: geometry dealt with 
constructions of geometric objects, algebra was concerned with algorithmic solutions to 
systems of equations, and analysis provided means to compute the future behavior of 
systems evolving over time. 

From the proof of a theorem, say, 'for every `x`, there is a `y` such that ...,' 
it was generally straightforward to extract an algorithm to compute such a `y` given `x`.

In the 19th century, however, increases in the complexity of mathematical arguments pushed 
mathematicians to develop new styles of reasoning that suppress algorithmic information 
and invoke descriptions of mathematical objects that abstract away the details of how 
those objects are represented. The goal was to obtain a powerful 'conceptual' understanding 
without getting bogged down in computational details, but this had the effect of admitting 
mathematical theorems that are simply *false* on a direct computational reading.

There is still fairly uniform agreement today that computation is important to mathematics. 
But there are different views as to how best to address computational concerns. 

From a *constructive* point of view, it is a mistake to separate mathematics from its 
computational roots; every meaningful mathematical theorem should have a direct 
computational interpretation. 

From a *classical* point of view, it is more fruitful to maintain a separation of concerns: 
we can use one language and body of methods to write computer programs, while maintaining 
the freedom to use a nonconstructive theories and methods to reason about them. 

Lean is designed to support both of these approaches. Core parts of the library are 
developed constructively, but the system also provides support for carrying out classical 
mathematical reasoning.

Computationally, the purest part of dependent type theory avoids `Prop` entirely. Inductive 
types and dependent function types can be viewed as data types, and terms of these types 
can be 'evaluated' by applying reduction rules until no more rules can be applied. In 
principle, any closed term (that is, term with no free variables) of type `ℕ` should 
evaluate to a numeral, `succ (... (succ zero)...)`.

Introducing a proof-irrelevant `Prop` and marking theorems irreducible represents a first 
step towards separation of concerns. The intention is that elements of a type `p : Prop` 
should play no role in computation, and so the particular construction of a term 
`t : p` is 'irrelevant' in that sense. One can still define computational objects that 
incorporate elements of type `Prop`; the point is that these elements can help us reason 
about the effects of the computation, but can be ignored when we extract 'code' from the term. 

Elements of type `Prop` are not entirely innocuous, however. They include equations 
`s = t : α` for any type `α`, and such equations can be used as casts to type check terms. 
Below, we will see examples of how such casts can block computation in the system. However, 
computation is still possible under an evaluation scheme that erases propositional content, 
ignores intermediate typing constraints, and reduces terms until they reach a normal form. 
This is precisely what Lean's virtual machine does.

Having adopted a proof-irrelevant ``Prop``, one might consider it legitimate to use, for 
example, the law of the excluded middle, ``p ∨ ¬p``, where ``p`` is any proposition. 
Of course, this, too, can block computation according to the rules of CIC, but it does not 
block bytecode evaluation, as described above. It is only the choice principles that 
completely erase the distinction between the proof-irrelevant and data-relevant parts of 
the theory."


#print "
Section 11.2. Propositional Extensionality
------------------------------------------ "

namespace Sec_11_2
  #print "Propositional extensionality is the `propext` axiom,"
  axiom propext {a b : Prop} : (a ↔ b) → a = b
  #print "asserting that when two props imply one another, they are equal. This is 
  consistent with set-theoretic interpretations in which any element `a : Prop` is either 
  empty (false) or the singleton set `{*}` (true), for some distinguished element `*`. 
  The effect is that equivalent props can be substituted for one another in any context."
  variables a b c d e : Prop
  variable p : Prop → Prop

  theorem thm₁ (h : a ↔ b) : (c ∧ a ∧ d → e) ↔ (c ∧ b ∧ d → e) := propext h ▸ iff.refl _

  theorem thm₂ (h : a ↔ b) (hpa : p a) : p b := propext h ▸ hpa

  #print "The first example could be proved more laboriously without `propext` using the 
  fact that the propositional connectives respect propositional equivalence. 
  The second example represents a more essential use of `propext`. In fact, it is 
  equivalent to `propext` itself. (Exercise)"

  -- Solution:
  theorem propext_equiv {a b : Prop} : 
  ((a ↔ b) → a = b) ↔ (∀ (P : Prop → Prop), (a ↔ b) → (P a ↔ P b)) := iff.intro
  (assume h: (a ↔ b) → a = b, show (∀ (P : Prop → Prop), (a ↔ b) → (P a ↔ P b)), from
    assume (P : Prop → Prop) (hab : a ↔ b), 
    have heq : a = b, from h hab, 
    have hab : P a = P b, from congr_arg P heq,
    iff.intro (assume hpa : P a, show P b, from hab ▸ hpa )
    (assume hpb : P b, show P a, by simp [hpb, hab]))
  (assume h: (∀ (P : Prop → Prop), (a ↔ b) → (P a ↔ P b)),
    assume hc : a ↔ b, show a = b, by rw hc)
 
  #print "Given any definition or theorem in Lean, you can use the `#print axioms` command 
  to display the axioms it depends on."
  
  #print axioms thm₁ 
  #print axioms thm₂ 

end Sec_11_2


#print "
Section 11.3. Function Extensionality
====================================="

namespace Sec_11_3
  #print "Function extensionality asserts that any two functions of type `Π x : α, β x` that 
  agree on all inputs are equal."
  universes u₁ u₂ 
  #check (@funext : ∀ {α : Type u₁} { β : α → Type u₂ } {f₁ f₂ : Π (x : α), β x},
          (∀ (x : α), f₁ x = f₂ x) → (f₁ = f₂))

  #print "From a classical, set-theoretic perspective, this is exactly what it means for 
  two functions to be equal. This is known as an 'extensional' view of functions. From a 
  constructive perspective, however, it is sometimes more natural to think of functions as 
  algorithms, or computer programs, that are presented in some explicit way. It is certainly 
  the case that two computer programs can compute the same answer for every input despite 
  the fact that they are syntactically quite different. In much the same way, you might want 
  to maintain a view of functions that does not force you to identify two functions that 
  have the same i/o behavior. This is known as an 'intensional' view of functions.
  
  In fact, function extensionality follows from the existence of quotients, which we 
  describe in the next section. In the Lean stdlib, therefore, `funext` is 
  [proved from the quotient 
  construction](https://github.com/leanprover/lean/blob/master/library/init/funext.lean).

  Suppose `α : Type` and let `set α := α → Prop` denote the type of subsets of `α`, 
  identifying subsets with predicates. By combining `funext` and `propext`, we obtain an 
  extensional theory of such sets."

  universe u
  def set (α : Type u) := α → Prop

  namespace set
  variable {α : Type u}

  def mem (x : α) (a : set α) := a x
  -- notation e ∈ a := mem e a

  instance has_mem_set (α : Type u) : has_mem α (set α) := ⟨mem⟩ 

  theorem setext {a b : set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b := 
  funext (assume x, propext (h x))

  #print "We can then proceed to define the empty set and set intersection and prove set identities."

  def empty : set α := λ a, false
  local notation `∅` := empty 

  def intersection (a b : set α) : set α := λ x, x ∈ a ∧ x ∈ b
  notation a ∩ b := intersection a b
  theorem intersection_is_idempotent (a : set α) : a ∩ a = a := 
  setext (assume x, and_self _)

  #check and_self -- ∀ (a : Prop), a ∧ a ↔ a    (from the stdlib)

  theorem meet_of_zero (a : set α) : a ∩ ∅ = ∅ := 
  setext (assume x, and_false _)
  
  #check and_false -- ∀ (a : Prop), a ∧ false ↔ false   (from the stdlib)

  theorem zero_of_meet (a : set α) : ∅ ∩ a = ∅ := 
  setext (assume x, false_and _)

  theorem intersection_is_commutative (a b : set α) : a ∩ b = b ∩ a := 
  setext (assume x, and_comm _ _)
 
  end set

  #print "
  Here's an example of how function extensionality can block computation in the Lean kernel."

  def f₁ (x : ℕ) := x
  def f₂ (x : ℕ) := 0 + x

  theorem feq : f₁ = f₂ := funext (assume x, (zero_add x).symm)

  def val : ℕ := eq.rec_on feq (0 : ℕ)
  #reduce val
  -- #eval val
  #print "First, we show that the two functions `f₁` and `f₂` are equal using function 
  extensionality, and then we cast `0` of type `ℕ` by replacing `f₁` by `f₂` in the type. 
  Of course, the cast is vacuous, because `ℕ` doesn't depend on `f₁`. But that is enough 
  to do the damage: under the computational rules of the system, we now have a closed 
  term of `ℕ` that does not reduce to a numeral. In this case, we may be tempted to reduce 
  the expression to `0`. But in nontrivial examples, eliminating cast changes the type of 
  the term, which might make an ambient expression type incorrect. The virtual machine, 
  however, has no trouble evaluating the expression to `0`."
  
  #print "Here's a similarly contrived example showing how `propext` gets in the way."
  theorem tteq : (true ∧ true) = true := propext (and_true true)

  def val₂  : ℕ := eq.rec_on tteq 0

  #reduce val₂ 
  #eval val₂ 

  #print "Current research programs, including work on *observational type theory* and 
  *cubical type theory*, aim to extend type theory in ways that permit reductions for casts 
  involving function extensionality, quotients, and more. But the solutions are not so 
  clear cut, and the rules of Lean's underlying calculus do not sanction such reductions.

  In a sense, however, a cast does not change the meaning of an expression. Rather, it is a 
  mechanism to reason about the expression's type. Given an appropriate semantics, it then 
  makes sense to reduce terms in ways that preserve their meaning, ignoring the intermediate
  bookkeeping needed to make the reductions type-correct. In that case, adding new axioms 
  in `Prop` does not matter; by proof irrelevance, an expression in `Prop` carries no 
  information, and can be safely ignored by the reduction procedures."



end Sec_11_3


#print "
Section 11.4. Quotients
======================="

#print "
Let `α` be a type, and `r` an equivalence relation on `α`. It is mathematically common to 
form the 'quotient' `α / r`, that is, the type of elements of `α` 'modulo' `r`. 
Set theoretically, one can view `α / r` as the set of equivalence classes of `α` modulo 
`r`. 

If `f : α → β` is a function that respects the equivalence relation, then `f` 'lifts' to a 
function `f' : α / r → β` defined on each equivalence class `⟦x⟧` by `f' ⟦x⟧ = f x`. 
Lean's stdlib extends CiC with additional constants that perform exactly these constructions,
and installs this last equation as a definitional reduction rule.

In its most basic form, the quotient construction does not even require `r` to be an 
equivalence relation."


namespace Sec_11_4
  universes u v

  #print "The following constants and axiom are built into Lean."

  constant quot : Π {α : Sort u}, (α → α → Prop) → Sort u
  -- form the quotient, `quot r`, induced by the relation `r ⊆ α × α`, 

  constant quot.mk : Π {α : Sort u} (r : α → α → Prop), α → quot r
  -- map `α` to `quot α`, so if `a : α`, then `quot.mk a`` is an element of `quot r`.

  axiom quot.ind : ∀ {α : Sort u} {r : α → α → Prop} {β : quot r → Prop},
    (∀ a, β (quot.mk r a)) → ∀ (q: quot r), β q
  -- `quot.ind`, says that every element of `quot.mk a` is of this form. 

  constant quot.lift : Π {α : Sort u} {r : α → α → Prop} {β : Sort u} (f : α → β),
    (∀ a b , r a b → f a = f b) → quot r → β 

  #print "`quot.lift` says, given a function `f : α → β`, if `h` is a proof 
  that `f` respects the relation `r`, then `quot.lift f h` is the corresponding 
  function on `quot r`. That is, for each `a : α``, `quot.lift f h` maps `quot.mk r a` 
  (the `r`-class containing `a`) to `f a`, wherein `h` shows that this function is well 
  defined. "
  
end Sec_11_4

#print "In fact, the computation principle is declared as a reduction rule, as the proof below 
makes clear."
variables (α β : Type) (a : α) (r : α → α → Prop)

-- the quotient type 
#check (quot r : Type)

-- the r-class containing a
#check (quot.mk r a : quot r)

variables (f : α → β) (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂)

-- the corresponding function on quot r
#check (quot.lift f h : quot r → β)

-- the computation principle 
theorem computation_principle : quot.lift f h (quot.mk r a ) = f a := rfl

#print "The four constants, `quot`, `quot.mk`, `quot.ind`, and `quot.lift` in and of 
themselves are not very strong. You can check that the `quot.ind` is satisfied if we 
take `quot r` to be simply `α`, and take `quot.lift` to be the identity function 
(ignoring `h`). For that reason, these four constants are not viewed as additional axioms."
#print axioms computation_principle -- no axioms

#print "They are, like inductively defined types and the associated constructors and recursors,
viewed as part of the logical framework. What makes the `quot` construction into a bona 
fide quotient is the following additional axiom."

namespace  Sec_11_4
axiom quot.sound : ∀{α : Type}{r : α → α → Prop}{a b : α}, r a b → quot.mk r a = quot.mk r b

#print "That is, two elements of `α` related by `r` are identified in the quotient. 
If a theorem or definition makes use of `quot.sound`, it will show up in the `#print axioms` 
command. Of course, the quotient is most commonly used when `r` is an equiv rel. 
Given `r` as above, if we define `r'` according to the rule `r' a b` iff 
`quot.mk r a = quot.mk r b`, then it's clear that `r'` is an equivalence relation. 
(Indeed, `r'` is the *kernel* of the function ``a ↦ quot.mk r``.) 
The axiom ``quot.sound`` says that ``r a b`` implies ``r' a b``. Using ``quot.lift`` and 
``quot.ind``, we can show that `r'` is the *smallest* equivalence relation containing `r`; 
indeed, if `r''` is an equivalence relation containing `r`, then `r' a b` implies `r'' a b`. 
In particular, if `r` is already an equivalence relation, then for all `a` and `b` we have 
`r a b` iff `r' a b`.

To support this common use case, the standard library defines the notion of a *setoid*, which is simply a type with an associated equivalence relation:"


end Sec_11_4



#print "==========================================="
#print "Section 11.5. Choice"
#print " "

namespace Sec_11_5

end Sec_11_5


#print "==========================================="
#print "Section 11.6. The Law of the Excluded Middle"
#print " "

namespace Sec_11_6

end Sec_11_6


