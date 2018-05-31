-- 7. Inductive Types
/- Intuitively, an inductive type is built up from a specified list of constructors. 
   In Lean, the syntax for specifying such a type is as follows:

     inductive foo : Sort u
     | constructor₁ : ... → foo
     | constructor₂ : ... → foo
     ...
     | constructorₙ : ... → foo

   Intuition: each constructor specifies a way of building new objects of type `foo`, 
   possibly from previously constructed values. The type `foo` consists of nothing more 
   than the objects that are constructed in this way. The first character `|` is optional. 
   Also, we could separate constructors using commas instead of bars.

   Arguments to constructors can include objects of type `foo`, subject to a certain "positivity" 
   constraint, which guarantees that elements of `foo` are built from the bottom up. 
   Roughly speaking, each `...` can be any Pi type constructed from `foo` and previously defined 
   types, in which `foo` appears, if at all, only as the "target" of the Pi type. 

   Besides inductive types, we'll see generalizations, like mutually defined inductive types and 
   *inductive families*.
-/
#print "==========================================="
#print "Section 7.1. Enumerated Types"
#print " "
-- https://leanprover.github.io/theorem_proving_in_lean/inductive_types.html#enumerated-types

namespace Sec_7_1

  -- Every inductive type comes with 
  --   - introduction rules: show how to construct an element of the type; 
  --   - elimination rules: show how to “use” an element of the type in another construction. 
  -- Recall, intro rules for inductive types are the constructors specified in the types' defn. 
  -- Elimination rules provide for a principle of recursion on the type, which includes, 
  --   as a special case, a principle of induction as well.

  -- The simplest kind of inductive type is a finite, enumerated list of elements.
  inductive weekday : Type
  | Sunday : weekday
  | Monday : weekday
  | Tuesday : weekday
  | Wednesday : weekday
  | Thursday : weekday
  | Friday : weekday
  | Saturday : weekday
  -- Sunday, Monday, ..., Saturday are distinct elements of weekday, with no special properties.

  #check weekday.Monday
  section 
    open weekday
    #check Monday
  end
  /- The elimination principle `weekday.rec` is defined with `weekday` and its constructors. 
     `weekday.rec` is also known as a recursor; it's what makes the type "inductive" and allows 
     us to define a function on weekday by assigning values corresponding to each constructor. 
     Intuition: an inductive type is exhaustively generated by its constructors, and has no 
     elements beyond those they construct. -/

  -- We will use a variant of `weekday.rec`, `weekday.rec_on` (also generated automatically), 
  -- which takes its arguments in a more convenient order.

  -- Let's import `nat` and use `weekday.rec_on` to define a fun from weekday to natural numbers:
  namespace weekday₁
    def number_of_day (d : weekday) : ℕ := weekday.rec_on d 1 2 3 4 5 6 7
    #reduce number_of_day weekday.Sunday  -- result: 1
  end weekday₁
  /- The first (explicit) argument to `rec_on` is the element `d` being "analyzed." 
     The next seven arguments are the values corresponding to each of the seven constructors. 
     `number_of_day Sunday` evaluates to 1: the computation rule for `rec_on` sees that 
     `Sunday` is a constructor, and returns the appropriate argument. -/

  -- A more restricted variant is `cases_on`; for enumerated types, it's the same as `rec_on`, but 
  -- `cases_on` emphasizes that the definition is by cases.

  def number_of_day' (d : weekday) : ℕ := weekday.cases_on d 1 2 3 4 5 6 7

  -- It is useful to group related definitions and theorems in a single namespace. 
  -- We can put `number_of_day` in the `weekday` namespace and then use the shorter 
  -- name when we open the namespace.

  -- `rec_on` and `cases_on` are generated automatically, but are protected to avoid name clashes. 
  -- They're not provided by default when a namespace is opened, but we can declare aliases for 
  -- them with `renaming`

  namespace weekday
    @[reducible] private def cases_on := @weekday.cases_on
    def number_of_day (d : weekday) : ℕ := cases_on d 1 2 3 4 5 6 7
  end weekday

  #reduce weekday.number_of_day weekday.Monday
  -- #reduce number_of_day Sunday  -- error: unknown identifier
  -- #check @cases_on              -- error: unknown identifier
  open weekday (renaming cases_on → cases_on)  -- now we have an alias
  #reduce number_of_day Sunday
  #check @cases_on                    -- so we can use (unqualified) cases_on 

  namespace weekday   -- We can define functions from weekday to weekday:
    def next (d : weekday) : weekday :=
      weekday.cases_on d Monday Tuesday Wednesday Thursday Friday Saturday Sunday

    def previous (d : weekday) : weekday :=
      weekday.cases_on d Saturday Sunday Monday Tuesday Wednesday Thursday Friday 

    #reduce next (next Tuesday)
    #reduce next (previous Tuesday)

    example : next (previous Tuesday) = Tuesday := rfl

    theorem next_previous (d : weekday) : next (previous d) = d := 
    weekday.cases_on d 
      (show next (previous Sunday) = Sunday, from rfl)
      (show next (previous Monday) = Monday, from rfl) -- etc...
      -- `show` is just for clarity; we could just use `rfl`, as we do for the remaining cases:
      rfl rfl rfl rfl rfl

    -- With tactics, we can be even more concise
    example (d : weekday) : next (previous d) = d := by apply weekday.cases_on d; refl

    -- We could equally well have used `rec_on`:
    example (d : weekday) : next (previous d) = d := by apply weekday.rec_on d; refl

    -- Notice that, under the propositions-as-types correspondence, we can use `cases_on` to 
    -- prove theorems as well as define functions. 

  end weekday
end Sec_7_1

  -- Some fundamental data types in the Lean library are instances of enumerated types.
namespace hideme  -- use `hide₁` to avoid conflicts with stdlib.
  inductive empty : Type  -- an inductive data type with no constructors
  inductive unit : Type | star : unit
  inductive bool : Type | ff : bool | tt : bool
end hideme

    /- As an exercise, think about the introduction and elimination rules for these types,
       and define boolean operations `band`, `bor`, `bnot` on the boolean, and verifying 
       common identities; e.g., define `band` using a case split: -/
namespace hideme
  open hideme.bool   (renaming cases_on → cases_on)
  def b_and (b1 b2 : bool) : bool := cases_on b1 ff b2
  def b_or (b1 b2 : bool) : bool := cases_on b1 b2 tt 
  def b_not (b : bool) : bool := cases_on b tt ff 
  #reduce b_and tt tt   -- result: tt
  #reduce b_and ff tt   -- result: ff
  #reduce b_or tt ff    -- result: tt
  #reduce b_or ff ff    -- result: ff
  #reduce b_not ff      -- result: tt
  #reduce b_not tt      -- result: ff
end hideme
-- Similarly, most identities can be proved by introducing suitable case splits followed by `rfl`.

#print "==========================================="
#print "Section 7.2. Constructors with Arguments"
#print " "

namespace Sec_7_2
/- Enumerated types are a special case of inductive types, in which constructors take 
   no arguments. In general, a "construction" can depend on data, which is then represented 
   in the constructed argument. Consider the definitions of the product and sum types. -/

  universes u v
  namespace hide₂
    inductive prod (α : Type u) (β : Type v) | mk : α → β → prod
    inductive sum (α : Type u) (β : Type v) | inl {} : α → sum | inr {} : β → sum
  end hide₂
  
  /- To define a function on prod α β, we assume input of the form prod.mk a b, and specify
     the output in terms of a and b. For example, here is the definition of the two projections 
     for prod.  -/
  -- namespace custom_fst_snd
  --   open hide₂.prod (renaming rec_on → rec_on)
  --   -- def fst {α : Type u} {β : Type v} (p : prod α β) : α := rec_on p (λ a b, a)
  --   -- def snd {α : Type u} {β : Type v} (p : prod α β) : β := rec_on p (λ a b, b)
  -- end custom_fst_snd

  -- We could also use the std lib α × β and (a, b) (notation for prod α β and prod.mk a b, resp)
  namespace hide₃
    def fst {α : Type u} {β : Type v} (p : α × β) : α := prod.rec_on p (λ a b, a)
    def snd {α : Type u} {β : Type v} (p : α × β) : β := prod.rec_on p (λ a b, b)
    /- `fst` takes pair `p`, applies recursor `prod.rec_on p (λ a b, a)`---which interprets 
      `p` as pair `prod.mk a b`---then uses the 2nd arg to determine what to do with a and b. -/

    -- another example
    def prod_example₁ (p : bool × ℕ) : ℕ := prod.rec_on p (λ b n, cond b (2 * n) (2 * n + 1))
    #reduce prod_example₁ (tt, 3)  -- result: 6
    #reduce prod_example₁ (ff, 3)  -- result: 7

    -- `cond` has the same effect as `bool.rec_on b t2 t1` (note the transposition of t2 t1)
    def prod_example₂ (p: bool × ℕ): ℕ:= prod.rec_on p (λ b n, bool.rec_on b (2 * n + 1) (2 * n))
    #reduce prod_example₂ (tt, 3)  -- result: 6
    #reduce prod_example₂ (ff, 3)  -- result: 7

    def prod_example₃ (p : bool × ℕ) : ℕ := if (p.fst) then 2* p.snd else 2* p.snd + 1
    #reduce prod_example₃ (tt, 3)  -- result: 6
    #reduce prod_example₃ (ff, 3)  -- result: 7

    /- `sum` has two constructors, `inl` and `inr` and each takes one explicit argument. 
      To define a function on `sum α β`, we must handle 2 cases: if the input is of the form
      `inl a` (resp., `inr b`) then we must specify an output value in terms of a (resp `b`). -/

    def sum_example (s : ℕ ⊕ ℕ) : ℕ := sum.cases_on s (λ n, 2*n) (λ n, 2*n + 1)

    #reduce sum_example (sum.inl 3) -- result: 6
    #reduce sum_example (sum.inr 3) -- result: 7
  end hide₃

  /- A type with multiple constructors is *disjunctive*; e.g. an element of `sum α β` is either 
     of the form ``inl a`` *or* of the form ``inl b``. Further, each constructor with multiple 
     arguments introduces conjunctive information; e.g., from an element `prod.mk a b` of 
     `prod α β` we can extract `a` *and* `b`. An arbitrary inductive type can include both 
     features, by having any number of constructors, each of which takes any number of arguments.
  -/

  -- Lean's inductive definition syntax allows named arguments to constructors before the colon.
  namespace custom_prod₂
    -- instead of `inductive prod (α : Type u) (β : Type v) | mk : α → β → prod`
    -- we could have used
    inductive prod (α : Type) (β : Type) | mk (fst : α) (snd : β) : prod
    inductive sum (α : Type) (β : Type) | inl {} (a : α) : sum | inr {} (b : β) : sum
    -- These result in essentially the same types as before. `{}` refers to params, `α` and `β`.

    -- The following gives errors because naming fst and snd is not the same as defining them.
    --   def prod_example₄ (p : prod bool ℕ) : ℕ := if (p.fst) then 2* p.snd else 2* p.snd + 1
    --   #reduce prod_example₄ (prod.mk tt 3)  
    -- See the fix in custom_prod₃ below
  end custom_prod₂

  /- A type, like `prod`, that has only one constructor is purely conjunctive: 
     the constructor simply packs the list of arguments into a single piece of data, 
     essentially a tuple where 

       *THE TYPE OF SUBSEQUENT ARGUMENTS CAN DEPEND ON THE TYPE OF THE INITIAL ARGUMENT*

     We can think of such a type as a "record" or a "structure."  -/

  /- In Lean, the keyword `structure` can be used to define such an inductive type, as well 
     as its projections, at the same time. -/
  namespace custom_prod₃
    structure prod (α β : Type) := mk :: (fst : α) (snd : β)
    /- This simultaneously introduces the inductive type, `prod`, its constructor, `mk`, the
       usual eliminators (`rec` and `rec_on`), as well as the projections, `fst` and `snd`.
       So our previous example, from `custom_prod`, works now. -/
    def prod_example₄ (p : prod bool ℕ) : ℕ := if (p.fst) then 2* p.snd else 2* p.snd + 1
    #reduce prod_example₄ (prod.mk tt 3)  
    #reduce prod_example₄ (prod.mk ff 3)  

  end custom_prod₃

  /- If you don't name the constructor, Lean uses `mk` as a default. For example, the 
     following defines a record to store a color as a triple of RGB values: -/

  structure color := (red : ℕ) (green : ℕ) (blue : ℕ)
  def yellow := color.mk 255 255 0
  #reduce color.red yellow     -- result: 255  (`color.red` is projection onto first component)
  #reduce color.green yellow   -- result: 255
  #reduce color.blue yellow    -- result: 0

  /- ALGEBRAIC STRUCTURES. -/

  -- `structure` IS ESPECIALLY USEFUL FOR DEFINING ALGEBRAIC STRUCTURES
  -- and Lean provides substantial infrastructure to support working with them. 

  -- SEMIGROUPS --
  structure Semigroup := (univrs : Type u) 
    (mul : univrs → univrs → univrs)
    (mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c))

  -- ==> More examples in CHAPTER 9!!!!!!! <==
  -- (okay, but we should insert a short example of instantiating a semigroup here)
  def mysg := Semigroup.mk nat (λ x y, x * y)
  #check mysg

  -- Let's try to define lattices on our own, using what we already know.

  -- LATTICES --
  structure Lattice := (univrs : Type u)
    (meet: univrs → univrs → univrs)
    (join: univrs → univrs → univrs)
    (idempotent_meet : ∀ x,  meet x x = x)
    (idempotent_join : ∀ x,  join x x = x)
    (commutative_meet : ∀ x y, meet x y = meet y x)
    (commutative_join : ∀ x y, join x y = join y x)
    (associative_meet : ∀ x y z, meet (meet x y) z = meet x (meet y z))
    (associative_join : ∀ x y z, join (join x y) z = join x (join y z))
    (absorptive_meet : ∀ x y, meet x (join x y) = x)
    (absorptive_join : ∀ x y, join x (meet x y) = x)

  -- Okay, fine, so now how do we *use* this structure to do lattice theory.
  ----------------------------------------------------------------------------
  def mylat := Lattice.mk nat (λ x y, if (x < y) then x else y) (λ x y, if (y < x) then x else y) 
  #check mylat

  -- Recall, sigma types are also known as the "dependent product" type:
  namespace hide₄
    inductive sigma {α : Type u} (β : α → Type v) | dpair : Π a : α, β a → sigma
    -- This looks confusing because sigma is not a pi type.  But the constructor
    -- is a function whose domain is a pi type and whose codomain is sigma.

    -- Two more inductive types in the library are `option` and `inhabited`.
    inductive option (α : Type u) | none {} : option | some    : α → option
    inductive inhabited (α : Type u) | mk : α → inhabited
  end hide₄

  -- `option` type enables us to define partial functions

  /- In the semantics of dependent type theory, there is no built-in notion of a partial 
     function. Every element of a function type `α → β` or a Pi type `Π x : α, β` is assumed 
     total. The `option` type enables us to represent partial functions. An element of 
     `option β` is either `none` or of the form `some b`, for some value `b : β`. Thus,
     `α → option β` is the type of partial functions from `α` to `β`; if `a : α`, then 
     `f a` either returns `none`, indicating the `f` is "undefined" at `a`, or `some b`. -/

  /- An element of `inhabited α` is simply a witness to existence of an element of `α`. 
     `inhabited` is actually an example of a **type class** in Lean: Lean can be told that
     suitable base types are inhabited, and can automatically infer that other constructed 
     types are inhabited on that basis. -/

  /- As exercises, develop a notion of composition for partial functions from `α` to `β` and 
     `β` to `γ`, and show that it behaves as expected. -/

  namespace exercise₁
    inductive option (α : Type u) | none {} : option | some : α → option
    def compose (α β γ: Type u) (f : α → option β) (g : β → option γ) (x: α) : option γ := 
      option.cases_on (f x) (option.none) (λ y, g y)
  end exercise₁

  /- Also, show that `bool` and `nat` are inhabited, that the product of two inhabited types
     is inhabited, and that the type of functions to an inhabited type is inhabited. -/
  namespace exercise₂
    inductive inhabited (α : Type u) | mk : α → inhabited
    theorem bool_is_inhabited : inhabited bool := inhabited.mk tt 
    theorem nat_is_inhabited : inhabited nat := inhabited.mk 0 
    #check bool_is_inhabited
    #check nat_is_inhabited
  end exercise₂

end Sec_7_2


#print "==========================================="
#print "Section 7.3. Inductively Defined Propositions"
#print " "
-- https://leanprover.github.io/theorem_proving_in_lean/inductive_types.html#inductively-defined-propositions

/- Inductively defined types can live in any type universe, including the bottom-most one, 
   `Prop`. In fact, this is exactly how the logical connectives are defined. -/

namespace Sec_7_3
  namespace hide₅
    inductive false : Prop
    inductive true : Prop | intro : true
    inductive and (a b : Prop) : Prop | intro : a → b → and
    inductive or (a b : Prop) : Prop | intro_left : a → or | intro_right : b → or

    -- Alternatively, we could give names to the inhabitants:
    inductive and' (P Q : Prop) : Prop | intro (a : P) (b : Q) : and'
    inductive or' (P Q : Prop) : Prop | inl (a : P) : or' | inr (b : Q) : or'

    variables p q: Prop
    #check @and.intro p
    #check @and.intro p q
    #check @and'.intro p
    #check @and'.intro p q
    #check @or.intro_left p
    #check @or'.inl p
  end hide₅

  -- Think about how these give rise to the intro and elim rules we've already seen.

  -- There are rules that govern what the eliminator of an inductive type can eliminate to;
  -- that is, what kinds of types can be the target of a recursor.

  /- Roughly speaking, what characterizes inductive types in Prop is that one can only 
     eliminate to other types in Prop. This agrees with the fact that if `p : Prop`, then
     an element `hp : p` carries no info. (There is one exception discussed below.) -/

  -- Even the existential quantifier is inductively defined:
  namespace hide₆
    universe u
    inductive Exists {α : Type u} (p : α → Prop) : Prop | intro : ∀(a : α), p a → Exists
    inductive Egzsts {α : Type u} (p : α → Prop) : Prop | intro (w : ∀(a : α), p a) : Egzsts
    def exists.intro := @Exists.intro

    variables (α : Type) (p : α → Prop) (a : α)

    #check @exists.intro
    #check @exists.intro α
    #check @exists.intro α p
    #check @exists.intro α p a
  end hide₆

  -- The notation `∃ x : α, p` is syntactic sugar for `Exists (λ x : α, p)`.

  /- The defs of `false`, `true`, `and`, and `or` are analogous to the defs of 
     `empty`, `unit`, `prod`, and `sum`. The difference is the former yield
     elements of `Prop`, and the latter yield elements of `Type u` for some `u`. -/

  -- Similarly, `∃ x : α, p` is a `Prop`-valued variant of `Σ x : α, p`.

  /- Another inductive type, denoted `{x : α | p}`, is sort of a hybrid between 
     `∃ x : α, P` and `Σ x : α, P`. It is the `subtype` type. -/

  namespace hide₇
    universe u
    inductive subtype {α : Type u} (p : α → Prop) | mk : Π(x : α), p x → subtype

    inductive subtype_alt {α : Type u} (p : α → Prop) | mk (w : Π(x : α), p x) : subtype_alt
  end hide₇

 -- This next example is unclear to me.
 namespace confusing_example
   universe u
   variables {α : Type u} (p : α → Prop)
   --  ==========> UNRESOLVED QUESTIONS:     <==========
   #check subtype p        -- why is the result `subtype p : Type u` ??
   #check {x : α // p x }  -- why is the result `{x // p x } : Type u` ??
 end confusing_example
 -- The notation `{x : α // p x}` is syntactic sugar for subtype `(λ x : α, p x)`. 


end Sec_7_3

#print "==========================================="
#print "Section 7.4. Defining the Natural Numbers"
#print " "
-- https://leanprover.github.io/theorem_proving_in_lean/inductive_types.html#defining-the-natural-numbers

namespace hidden
  /- The inductively defined types we have seen so far are "flat": constructors wrap data and
     insert it into a type, and the corresponding recursor unpacks the data and acts on it. 
     Things get more interesting when constructors act on elements of the type being defined. -/

  -- -- A canonical example:
  -- namespace hide_7_4_1

  inductive nat : Type 
  | zero : nat 
  | succ : nat → nat

/- The recursor for `nat` defines a dependent function `f` from `nat` to any domain, 
   that is, `nat.rec` defines an element `f` of `Π n : nat, C n` for any `C : nat → Type`. 
   It has to handle two cases: the case where the input is zero, and the case where the 
   input is of the form succ n for some n : nat. 
   First case: we specify a target value of appropriate type. 
   Second case: the recursor assumes f(n) has been computed and then uses the 
   next argument to specify a value for f (succ n) in terms of n and f n. -/
 
  #check @nat.rec_on -- result:  Π {C : nat → Sort u_1} (n : nat), -- arg 1: major premise
                     --           C nat.zero →                     -- arg 2: minor premise 1
                     -- (Π (a : nat), C a → C (nat.succ a))        -- arg 3: specifies how to 
                     --                                                       construct f(n+1) 
                     --                                                       given n and f(n)
                     -- → C n                                      -- output type

  namespace nat
    def add (m n: nat): nat:= nat.rec_on n m               -- if n = zero, just return m
                              (λ n add_m_n, succ add_m_n)  -- otherwise, given n and the 
                                                           -- result (add_m_n := add m n), 
                                                           -- return add_m_n + 1

    #reduce add (succ zero) (succ (succ zero)) -- result: succ (succ (succ zero))

    -- Can we recurse on m instead of n?  Yes, of course.
    def add' (m n : nat) : nat := nat.rec_on m n (λ m add_m_n, succ add_m_n)
    #reduce add' (succ zero) (succ (succ zero)) -- same result as above

    /- Let's go back to the first definition of `add` and dissect it. 
       + `nat.rec_on n` says "recurse on n".  
       + The next symbol is `m` which gives the answer in base case: n=zero.  
       + The next group of symbols is `(λ n add_m_n, succ add_m_n)` which gives the answer
         in the inductive case. The first argument to the λ abstraction is `n`, which means 
         assume we know the value, `add_m_n`, that should be returned on input `m n`.
         Finally, use this to say what to do when the input is `m (succ n)`; namely,  
         return `succ add_m_n`. That's all there is to it! -/

    instance : has_zero nat := has_zero.mk zero
    instance : has_add nat := has_add.mk add

    theorem add_zero (m : nat) : m + 0 = m := rfl
    theorem add_succ (m n : nat) : m + succ n = succ (m + n) := rfl
  end nat

  end hidden

  /- Proving `0 + m = m`, however, requires induction. The induction principle is just a 
     special case of the recursion principle when the codomain `C n` is an element of `Prop`. 
     It represents the familiar pattern of proof by induction: to prove `∀ n, C n`, first
     prove `C 0`, and then, for arbitrary `n`, assume `ih : C n` and prove `C (succ n)`. -/
  namespace Sec_7_4
  open nat
  theorem zero_add (n : ℕ) : 0 + n = n := nat.rec_on n
    (show 0 + 0 = 0, from rfl)
    (assume n, assume ih : 0 + n = n,
      show 0 + succ n = succ n, from 
        calc
          0 + succ n = succ (0 + n) : rfl
                 ... = succ n : by rw ih)

  end Sec_7_4
  -- theorem zero_add (n : ℕ) : 0 + n = n := nat.rec_on n
  --   (show 0 + 0 = 0, from rfl)
  --   (assume n, assume ih : 0 + n = n,
  --     show 0 + succ n = succ n, from 
  --       calc
  --         0 + succ n = succ (0 + n) : rfl
  --                ... = succ n : by rw ih)

  namespace Sec_7_4
  open nat
  theorem zero_add' (n : ℕ) : 0 + n = n := nat.rec_on n 
  rfl (λ n ih, by simp only [add_succ, ih])
  /- Remarks: (1) when `nat.rec_on` is used in a proof, it's the induction principle in disguise. 
     The `rewrite` and `simp` tactics tend to be effective in proofs like these.
     (2) Leaving off the `only` modifier would be misleading because `zero_add` is declared 
     in the standard library. Using `only` guarantees `simp` uses only the identities listed.-/

  /- Associativity of addition: ∀ m n k, m + n + k = m + (n + k). 
     The hardest part is figuring out which variable to do the induction on. 
     Since addition is defined by recursion on the second argument, k is a good guess. -/
  theorem add_assoc (m n k : ℕ) : m + n + k = m + (n + k) := nat.rec_on k
    (show m + n + 0 = m + (n + 0), from rfl)
    (assume k, assume ih : m + n + k = m + (n + k), 
      show (m + n) + succ k = m + (n + succ k), from
        calc (m + n) + succ k = succ ((m + n) + k) : rfl
                          ... = succ (m + (n + k)) : by rw ih
                          ... = m + succ (n + k) : rfl
                          ... = m + (n + succ k) : rfl)

  -- once again, there is a one-line proof
  theorem add_assoc' (m n k : ℕ) : m + n + k = m + (n + k) := nat.rec_on k
    rfl (λ k ih, by simp only [add_succ, ih])


  theorem succ_add (m n : ℕ) : succ m + n = succ (m + n) := nat.rec_on n
    (show succ m + 0 = succ (m + 0), from rfl)
     (assume n,
       assume ih : succ m + n = succ (m + n),
       show succ m + succ n = succ (m + succ n), from
         calc 
           succ m + succ n = succ (succ m + n) : rfl
                       ... = succ (succ (m + n)) : by rw ih
                       ... = succ (m + succ n) : rfl)

  -- Commutativity of addition:
  theorem add_comm (m n : ℕ) : m + n = n + m := nat.rec_on n
   (show m + 0 = 0 + m, by rw [nat.zero_add, nat.add_zero])
   (assume n,
     assume ih : m + n = n + m,
     show m + succ n = succ n + m, from
       calc 
         m + succ n = succ (m + n) : rfl
                ... = succ (n + m) : by rw ih
                ... = succ n + m : by simp only [succ_add])

  -- Here are the shorter versions of the last two theorems:
  theorem succ_add' (m n : ℕ) : succ m + n = succ (m + n) := 
  nat.rec_on n rfl (λ n ih, by simp only [succ_add, ih])

  theorem add_comm' (m n : ℕ) : m + n = n + m := nat.rec_on n 
    (by simp only [zero_add, add_zero])
    (λ n ih, by simp only [add_succ, ih, succ_add])

--  end hide_7_4_2

end Sec_7_4


#print "==========================================="
#print "Section 7.5. Other Recursive Data Types"
#print " "
-- https://leanprover.github.io/theorem_proving_in_lean/inductive_types.html#other-recursive-data-types

-- Here are some more examples of inductively defined types.
namespace Sec_7_5
  -- For any type, α, the type list α of lists of elements of α is defined in the library.
  universe u
  inductive my_list (α : Type u)
  | nil {} : my_list
  | cons : α → my_list → my_list

  namespace my_list
  
  variable {α : Type}
  
  notation h :: t := cons h t

  def append (s t : my_list α) : my_list α := 
    my_list.rec t (λ (x: α) (l: my_list α) (u: my_list α), x :: u) s
  /- Dissection of append: 
     The first arg to `list.rec` is `t`, meaning return `t` when `s` is `null`.
     The second arg is `(λ x l u, x :: u) s`.  I *think* this means the following:
     assuming `u` is the result of `append l t`, then `append (x :: l) t` results
     in `x :: u`.  
  -/

  /- To give some support for the claim that the foregoing interpretation is (roughtly) 
     correct, let's make the types explicit and verify that the definition still type-checks: -/
  def append' (s t : my_list α) : my_list α := 
    my_list.rec (t: my_list α) 
                (λ (x : α) (l : my_list α) (u: my_list α), x :: u) (s : my_list α)

  def append_rec_on (s t : my_list α) : my_list α := 
    my_list.rec (t: my_list α) 
                (λ (x : α) (l : my_list α) (u: my_list α), x :: u) (s : my_list α)

  #check nil                       -- nil : list ?M_1
  #check (nil: my_list ℕ)         -- nil : list ℕ
  #check cons 0 nil                -- 0 :: nil : list ℕ
  #check cons "a" nil              -- 0 :: nil : list string
  #check cons "a" (cons "b" nil)   -- a :: b :: nil : list string

  notation s ++ t := append s t

  theorem nil_append (t : my_list α) : nil ++ t = t := rfl

  theorem cons_append (x : α) (s t : my_list α) : (x :: s) ++ t = x :: (s ++ t) := rfl

  
  -- Lean allows us to define iterative notation for lists:

  notation `{` l:(foldr `,` (h t, cons h t) nil) `}` := l

  section
    open nat
    #check {1,2,3,4,5}               -- Lean assumes this is a list of nats
    #check ({1,2,3,4,5} : my_list int)  -- Forces Lean to take this as a list of ints.
  end 

  -- As an exercise, prove the following:
  theorem append_nil (t : my_list α) : t ++ nil = t := my_list.rec_on t 
    (show (append nil nil) = nil, from rfl)
    (assume (x : α), assume (t : my_list α),
     assume ih : (append t nil) = t,
     show append (x :: t) nil = (x :: t), from
       calc
         append (x :: t) nil = x :: append t nil  : cons_append x t nil
                         ... = x :: t             : by rw ih)

  -- As an exercise, prove the following:
  theorem append_nil' (t : my_list α) : t ++ nil = t := my_list.rec_on t 
    rfl  -- (base)
    (λ (x : α) (t : my_list α) (ih : (append t nil) = t), by simp [cons_append, ih]) -- (induct)

  --theorem append_assoc (r s t : my_list α) : r ++ s ++ t = r ++ (s ++ t) := sorry

  -- binary trees
  inductive binary_tree
  | leaf : binary_tree
  | node : binary_tree → binary_tree → binary_tree

  -- countably branching trees
  inductive cbtree
  | leaf : cbtree
  | sup : (ℕ → cbtree) → cbtree

  namespace cbtree
  
  def succ (t : cbtree) : cbtree := sup (λ n, t)  -- Note: (λ n, t) is a thunk; i.e., a way to
                                                  -- view t as a function of type ℕ → cbtree.

  /- Note the similarity to nat's successor.  The third cbtree after t would be 
     `sup (λ n, sup (λ n, sup (λ n, t))` -/

  def omega : cbtree := sup (λ n, nat.rec_on n leaf (λ n t, succ t))
  end cbtree
  end my_list
           
end Sec_7_5


#print "==========================================="
#print "Section 7.6. Tactics for Inductive Types"
#print " " 
-- https://leanprover.github.io/theorem_proving_in_lean/inductive_types.html#tactics-for-inductive-types

namespace Sec_7_6
  /- There are a number of tactics designed to work with inductive types effectively. 
     The `cases` tactic works on elements of an inductively defined type by decomposing 
     the element into the ways it could be constructed. -/

  namespace example₁
  variable p : ℕ → Prop
  open nat
  example (hz : p 0) (hs : ∀ n, p (succ n)) : ∀ n, p n :=
  begin
    intro n,
    cases n,
      exact hz,
      apply hs
  end
  
  /- `cases` lets you choose names for arguments to the constructors using `with`. 
     For example, we can choose the name `m` for the argument to `succ`, so the second 
     case refers to `succ m`. More importantly, `cases` detects items in the local context 
     that depend on the target variable. It reverts these elements, does the split, and 
     reintroduces them. In the example below, notice that `h : n ≠ 0` becomes `h : 0 ≠ 0` 
     in the first branch, and `h : succ m ≠ 0` in the second.-/

  example (n : ℕ) (h : n ≠ 0) : succ (pred n) = n :=
  begin
    cases n with m,  -- name cases using variable m
      -- goal: h : 0 ≠ 0 ⊢ succ (pred 0) = 0
      { apply (absurd rfl h) },
      -- goal: h : succ m ≠ 0 ⊢ succ (pred (succ m)) = succ m
      reflexivity
  end

  -- `cases` can be also be used to produce data and define functions.
  def f (n : ℕ) : ℕ := 
  begin cases n, exact 3, exact 7 end

  example : f 0 = 3 := rfl
  example : f 5 = 7 := rfl
  example : f 1000 = 7 := rfl
  -- in fact, we can prove that f n is constantly 7, except when n = 0.
  example  (n : ℕ) (h : n ≠ 0) : (f n) = 7 := begin
    cases n,
    { apply (absurd rfl h) },  -- goal: 0 ≠ 0 ⊢ f 0 = 7
    reflexivity                -- goal: (succ a ≠ 0) ⊢ f (succ a) = 7
  end
  end example₁
  -- Let's define a function that takes an single argument of type `tuple`.

  -- First define the type `tuple`.


  namespace functionals
  universe u
  open list

  -- Recall, we define a type that satisfies a predicate like this:

  def tuple (α : Type u) (n : ℕ) := subtype (λ (l : list α), (list.length l = n)) 
    -- { l : list α // list.length l = n }  -- (this didn't work for me) 

  variables {α : Type u} {n : ℕ}

  def f {n : ℕ} (t : tuple α n) : ℕ := begin cases n, exact 3, exact 7 end

  def my_tuple : tuple ℕ 3 := ⟨[0, 1, 2], rfl⟩

  example : f my_tuple = 7 := rfl

  -- As above, we prove that f t is constantly 7, except when t.length=0.
  example  (n : ℕ) (t : tuple α n) (h : n ≠ 0) : f t = 7 := 
  begin
    cases n,
    apply (absurd rfl h),  -- goal: 0 ≠ 0 ⊢ f 0 = 7
    reflexivity            -- goal: (a : ℕ) (succ a ≠ 0) (t : tuple α (succ a)) ⊢ f t = 7
  end

  end functionals

  namespace induction_tactic

  /- Just as `cases` is used to carry out proof by cases, the `induction` tactic is used 
     for proofs by induction. In contrast to `cases`, the argument to `induction` can only 
     come from the local context. -/

  open nat
  theorem zero_add (n : ℕ) : 0 + n = n :=
  begin
    induction n with n ih,
      refl,
      rw [add_succ, ih]
  end

  
  -- The `case` tactic identifies each case with named arguments, making the proof clearer:
  theorem zero_add' (n : ℕ) : 0 + n = n :=
  begin
    induction n,
    case zero { refl },
    case succ n ih { rw [add_succ, ih] }
  end

  theorem succ_add' (m n : ℕ) : (succ m) + n = succ (m + n) :=
  begin
    induction n,
    case zero { refl },
    case succ n ih { rw [add_succ, ih] }
  end

  theorem add_comm' (m n : ℕ) : m + n = n + m :=
  begin
    induction n,
    case zero { rw zero_add, refl },
    case succ n ih { rw [add_succ, ih, succ_add] }
  end

  -- Here are terse versions of the last three proofs.
  theorem zero_add'' (n : ℕ) : 0 + n = n := by induction n; simp only [*, add_zero, add_succ]

  theorem succ_add'' (m n : ℕ) : (succ m) + n = succ (m+n) := 
  by induction n; simp only [*, add_zero, add_succ]

  theorem add_comm'' (m n : ℕ) : m + n = n + m :=
  by induction n; simp only [*, zero_add, add_zero, add_succ, succ_add]

  theorem add_assoc'' (m n k : ℕ) : m + n + k = m + (n + k) :=
  by induction k; simp only [*, add_zero, add_succ]

  end induction_tactic

  namespace injection_tactic
  /-We close this section with one last tactic that is designed to facilitate working with 
    inductive types, namely, the injection tactic. By design, the elements of an inductive 
    type are freely generated, which is to say, the constructors are injective and have 
    disjoint ranges. The injection tactic is designed to make use of this fact:  -/
  end injection_tactic

end Sec_7_6


#print "==========================================="
#print "Section 7.7. Inductive Families"
#print " "

namespace Sec_7_7

end Sec_7_7


#print "==========================================="
#print "Section 7.8. Axiomatic Details"
#print " "

namespace Sec_7_8

end Sec_7_8


#print "==========================================="
#print "Section 7.9. Mutual and Nested Inductive Types"
#print " "

namespace Sec_7_9

end Sec_7_9


#print "==========================================="
#print "Section 7.10. Exercises"
#print " "

namespace Sec_7_10

end Sec_7_10


