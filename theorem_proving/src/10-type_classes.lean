#print "Chapter 10. Type Classes

We've seen that Lean's elaborator provides helpful automation, filling in information 
that is tedious to enter by hand. In this section we'll explore a simple but powerful 
technical device known as *type class inference*, which provides yet another mechanism 
for the elaborator to supply missing information.

*Type classes* originated with *Haskell*. In that context, type classes are often used 
to associate operations, like a canonical addition or multiplication, to a data type. 
This and other original uses carry over, but, as we will see, the realm of interactive 
theorem proving raises even more possibilities for their use."


#print "
Section 10.1. Type Classes and Instances
----------------------------------------

Any family of types can be marked as a *type class*. We can then declare particular 
elements of a type class to be *instances*. These provide hints to the elaborator: 
any time the elaborator is looking for an element of a type class, it can consult a 
table of declared instances to find a suitable element.

More precisely, there are three steps involved:

1. declare a family of inductive types to be a type class;
2. declare instances of the type class;
3. mark some implicit arguments with square brackets instead of curly brackets 
   to tell the elaborator to infer these arguments using the type class mechanism.

We start with an example scenario. 

Many theorems hold under the additional assumption that a type is inhabited, which 
is to say, it has at least one element. For example, if `α` is a type, then
`∃ x : α, x = x` holds iff `α` is inhabited. 

Similarly, we often want a definition to return a default element in a 'corner case.' 
For example, `head l` should be of type `α` when `l : list α`, but then we are faced 
with the problem that `head l` needs to return an 'arbitrary' element of type `α` when
`l` happens to be the empty list, `nil`.

The std lib defines the type class `inhabited : Type → Type` to enable type class 
inference to infer a 'default' or 'arbitrary' element of an inhabited type."

namespace Sec_10_1
  -- First, we declare an appropriate class.
  class inhabited (α : Type _) := (default : α)
  
  namespace hidden
  -- The command `class` above is shorthand for,
  @[class] structure inhabited (α : Type _) := (default : α)
  end hidden

  #print "
  An element of the class `inhabited α` is simply an expression of the form
  `inhabited.mk a`, for some element `a : α`. The projection `inhabited.default` 
  will allow us to 'extract' such an element of `α` from an element of `inhabited α`.

  The second step of the program is to populate the class with some instances."

  instance Prop_inhabited : inhabited Prop := inhabited.mk true
  instance bool_inhabited : inhabited bool := inhabited.mk tt
  instance nat_inhabited : inhabited nat := inhabited.mk 0
  instance unit_inhabited : inhabited unit := inhabited.mk ()

  #print "
  The Lean stdlib regularly uses the anonymous constructor to define instances.
  "
  namespace hidden
    instance Prop_inhabited : inhabited Prop := ⟨true⟩ 
    instance bool_inhabited : inhabited bool := ⟨tt⟩ 
    instance nat_inhabited : inhabited nat := ⟨0⟩ 
    instance unit_inhabited : inhabited unit := ⟨()⟩ 
  end hidden 

  #print "
  These declarations simply record the definitions `Prop_inhabited`, `bool_inhabited`, 
  `nat_inhabited`, and `unit_inhabited` on a list of instances. Whenever the elaborator
  is looking for a value to assign to an argument `?M` of type `inhabited α` for some 
  `α`, it can check the list for a suitable instance. For example, if it looking for an 
  instance of `inhabited Prop`, it will find `Prop_inhabited`.

  The final step of the program is to define a function that infers an element 
  `s : inhabited α` and puts it to use. 
  
  The following function simply extracts the corresponding element `a : α`."
  
  def default (α : Type) [s : inhabited α] : α := @inhabited.default α s

  #print "
  The effect is that, given a type expression `α`, whenever we write `default α`, 
  we are really writing `default α ?s`, leaving the elaborator to find a suitable value 
  for the metavariable `?s`. When the elaborator succeeds in finding such a value, it 
  has effectively produced an element of type `α`."

  #check default Prop 
  #check default unit -- etc.

  #reduce default Prop -- result: true
  #reduce default unit -- result: punit.star  (???)

  #print "
  Sometimes we want to think of the default element as being an *arbitrary* element, 
  whose specific value should not play a role in a proof. For that purpose, we can write 
  `arbitrary α` instead of `default α`. The definition of `arbitrary` is the same as that 
  of `default`, but is marked `irreducible` to discourage the elaborator from unfolding it. 
  This does not preclude proofs from making use of it, so `arbitrary` merely signals intent."

end Sec_10_1

namespace Sec_10_2
  #print "
  Section 10.2. Chaining Instances
  --------------------------------

  What makes type class inference powerful is that one can *chain* instances. That is, an 
  instance declaration can in turn depend on an implicit instance of a type class. 
  This causes class inference to chain through instances recursively, backtracking when 
  necessary, in a Prolog-like search.

  For example, if two types `α` and `β` are inhabited, then so are their product, their sum, 
  and the type of functions from one to the other."
  
  instance inhabited_prod {α β : Type} [inhabited α] [inhabited β] : inhabited (prod α β) :=
    inhabited.mk (default α, default β)

  #print "
  Similarly, we can inhabit function spaces with suitable constant functions."    

  instance inhabited_fun {α β : Type} [inhabited β] : inhabited (α → β) :=
    inhabited.mk (λ (a: α), default β)

  #check default (nat → nat × bool)
  #reduce default (nat → nat × bool) -- λ (a : ℕ), (0, tt)

  #print "
  As an exercise, define default instances for other types, such as sums and lists."

  -- default sum types
  instance inhabited_suml {α β : Type} [inhabited α] : inhabited (sum α β) :=
    inhabited.mk (sum.inl (default α))
  instance inhabited_sumr {α β : Type} [inhabited β] : inhabited (sum α β) :=
    inhabited.mk (sum.inr (default β))

  -- default lists
  instance inhabited_list {α : Type} [inhabited α] : inhabited (list α) := 
  inhabited.mk (list.cons (default α)  list.nil)

  #check @Sec_10_2.inhabited_suml
  #check @Sec_10_2.inhabited_sumr
  #reduce default (list nat) -- [0]

end Sec_10_2

#print "
Section 10.3. Inferring Notation
--------------------------------

We now consider the application of type classes that motivates their use in functional 
programming languages like Haskell, namely, to overload notation in a principled way. 

In Lean, the symbol `+` can be given unrelated meanings, which is sometimes called 
'ad-hoc' overloading. Typically, however, we use `+` to denote a binary function from 
a type to itself, that is, a function of type `α → α → α` for some `α`. 
  
We can use type classes to infer an appropriate addition function for suitable types. 
  
We will see in the next section that this is especially useful for developing algebraic 
hierarchies of structures in a formal setting.

The stdlib declares a type class `has_add α` as follows."

namespace Sec_10_3
  universes u v
  class has_add (α : Type u) := (add : α → α → α)
 
  def add {α : Type u} [has_add α] : α → α → α := has_add.add

  notation a `+` b := add a b

  #print "The class `has_add α` is supposed to be inhabited exactly when there is an 
  appropriate add function for `α`. The `add` function is designed to find an instance 
  of `has_add α` for the given type, `α`, and apply the corresponding binary add function. 
  The notation `a + b` thus refers to the addition that is appropriate to the type of `a` 
  and `b`. We can then declare instances for `nat`, and `bool`."

  instance has_add_nat : has_add nat := ⟨nat.add⟩ 
  -- Again, we could have used ⟨ nat.add ⟩ instead of `has_add.mk nat.add`.

  instance has_add_bool : has_add bool := ⟨bor⟩ -- could have used `has_add.mk bor` instead

  -- #check 2 + 2  (DOESN'T WORK!)
  #check add 2 2
  #reduce add 2 2         -- result: 4
  #check @Sec_10_3.has_add_bool
  #reduce @Sec_10_3.has_add_bool
  #reduce add tt ff       -- result: tt

  #print "
  As with `inhabited`, the power of type class inference stems not only from the fact that 
  the class enables the elaborator to look up appropriate instances, but also from the fact 
  that it can chain instances to infer complex addition operations. 
  
  For example, assuming that there are appropriate addition functions for types `α` and `β`, 
  we can define addition on `α × β` pointwise:"
  
  instance has_add_prod {α: Type u} {β : Type v} [has_add α] [has_add β] : has_add (α × β) :=
    ⟨λ ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ , ⟨ a₁ + a₂ , b₁ + b₂⟩⟩ 

  #reduce add (1, 2) (3, 4)  -- (4,6)

  #print "We can similarly define pointwise addition of functions."

  instance has_add_fun_first_try {α : Type u} {β : Type v} [has_add β] : has_add (α → β) :=
    ⟨λ (f g: α → β), (λ a, f a + g a)⟩ 

  instance has_add_fun {α : Type u} {β : Type v} [has_add β] : has_add (α → β) :=
    ⟨λ f g x, f x + g x⟩ 

  #reduce (λ x : nat, 1) + (λ x, 2)  -- result: λ (x : ℕ), 3 

  #print "
  As an exercise, try defining instances of `has_add` for lists; show they work as expected."
  
  def add_lists {α: Type u} [has_add α] : list α → list α → list α
        | xx [] := xx
        | [] yy := yy
        | (x::xs) (y::ys) := (x + y) :: (add_lists xs ys)

  instance has_add_list {α : Type u} [has_add α] : has_add (list α) := 
  ⟨ λ xx yy, add_lists xx yy⟩ 

  #reduce add [1,2,3] [4,5,6]
  
end Sec_10_3




#print "
Section 10.4. Decidable Propositions
------------------------------------

Let us consider another example of a type class defined in the standard library, namely 
the type class of `decidable` propositions. Roughly speaking, an element of `Prop` is said 
to be decidable if we can decide whether it is true or false. The distinction is only 
useful in constructive mathematics; classically, every proposition is decidable. But if 
we use the classical principle, say, to define a function by cases, that function will 
not be computable. Algorithmically speaking, the `decidable` type class can be used to 
infer a procedure that effectively determines whether or not the proposition is true. 
As a result, the type class supports such computational definitions when they are possible 
while at the same time allowing a smooth transition to the use of classical definitions 
and classical reasoning."

namespace Sec_10_4
  -- In the standard library, `decidable` is defined formally as follows.
  class inductive decidable (p : Prop) : Type
  | is_false : ¬p → decidable 
  | is_true  :  p → decidable

  #print "
  Logically speaking, having an element `t : decidable p` is stronger than having an 
  element `t : p ∨ ¬p`; it enables us to define values of an arbitrary type depending 
  on the truth value of `p`. For example, for the expression `if p then a else b` to 
  make sense, we need to know that `p` is decidable. That expression is syntactic sugar 
  for `ite p a b`, where `ite` is defined as follows:"
  
  def ite (c: Prop) [d: decidable c] {α : Type} (t e : α) : α := decidable.rec_on d 
      (λ hnc, e) -- what to do in the else case
      (λ hc, t)  -- what to do in the if-then case

  #print "
  The standard library also contains a variant of `ite` called `dite`, the *dependent* 
  if-then-else expression. It is defined as follows:"
  def dite (c: Prop) [d : decidable c] {α : Type} (t : c → α) (e : ¬c → α) : α := 
    decidable.rec_on d (λ (hnc : ¬c), e hnc) (λ (hc : c), t hc) 
    
  #print "
  That is, in `dite c t e`, we can assume `hc : c` in the 'then' branch, and `hnc : ¬ c` 
  in the 'else' branch. 
  
  To make `dite` more convenient to use, Lean allows us to write 
  
      if h : c then t else e
  
  instead of 
  
      dite c (λ h : c, t) (λ h : ¬ c, e)
  "

  #print "
  Without classical logic, we cannot prove that every proposition is decidable. But we can 
  prove that *certain* propositions are decidable. For example, we can prove the 
  decidability of basic operations like equality and comparisons on the natural numbers 
  and the integers. Moreover, decidability is preserved under propositional connectives."
  
  #check nat.decidable_eq
  #check nat.decidable_lt
  #check int.decidable_lt

  #check @and.decidable
  #check @or.decidable
  #check @not.decidable

  -- Thus we can carry out definitions by cases on decidable predicates on the nats.
  def step (a b x : ℕ ) : ℕ := if x < a ∨ x > b then 0 else 1

  set_option pp.implicit true
  #print definition step

  #print "
  Turning on implicit arguments shows that the elaborator has inferred the decidability 
  of the proposition `x < a ∨ x > b`, simply by applying appropriate instances."

  #print "
  With the classical axioms, we can prove that every proposition is decidable. You can 
  import the classical axioms and make the generic instance of decidability available 
  by including the following at the top of your file."
  open classical
  local attribute [instance] prop_decidable

  #print "
  Thereafter `decidable p` has an instance for every `p`, and the elaborator infers that 
  value quickly. Thus all theorems in the library that rely on decidability assumptions 
  are freely available when you want to reason classically."

  #print "
  The `decidable` type class also provides a bit of small-scale automation for proving 
  theorems. The stdlib introduces the following definitions and notation."
end Sec_10_4

namespace hidden
  open classical
  local attribute [instance] prop_decidable
  def as_true (c : Prop) [decidable c] : Prop := if c then true else false
  def of_as_true {c: Prop} [h₁ : decidable c] (h₂ : as_true c) : c := match h₁, h₂ with
    | (is_true h_c), h₂ := h_c
    | (is_false h_c), h₂ := false.elim h₂ 
  end 
  --notation `dec_trivial` := of_as_true (by tactic.triv)
  #print "
  These work as follows: The expression `as_true c` tries to infer a decision 
  procedure for `c`, and, if it is successful, evaluates to either `true` or `false`. 
  
  In particular, if `c` is a true closed expression, `as_true c` will reduce definitionally 
  to `true`. On the assumption that `as_true c` holds, `of_as_true` produces a proof of `c`. 
  The notation `dec_trivial` puts it all together.
  
  ~~>  To prove `c`, apply `of_as_true`, then use the `triv` tactic to prove `as_true c`. 
  
  By the previous observations, `dec_trivial` will succeed any time the inferred decision 
  procedure for `c` has enough information to evaluate, definitionally, to the `is_true` 
  case. "
-- Here is an example of how `dec_trivial` can be used.
end hidden

example : 1 ≠ 0 ∧ (5 < 2 ∨ 3 < 7) := dec_trivial

#print "
Section 10.5. Managing Type Class Inference
-------------------------------------------"

namespace Sec_10_5

  -- Lean can tell you about the classes and instances that are currently in scope."
  #print classes
  #print add_monoid
  #print partial_order
  #print preorder

  #print "You sometimes find the type class inference fails to find an expected instance, 
  or, worse, falls into an infinite loop and times out. To help debug in these situations, 
  Lean enables you to request a trace of the search:"

  set_option trace.class_instances true

  #print "With this in your file, in Emacs mode, `C-c C-x` runs an independent Lean process 
  on your file, and the output buffer will show a trace every time the type class resolution 
  procedure is subsequently triggered.

  You can also limit the search depth (the default is 32)."
  set_option class.instance_max_depth 5

  #print "In the Emacs `lean-mode`, tab completion works in `set_option`, to help you 
  find suitable options.

  As noted above, the type class instances in a given context represent a Prolog-like 
  program, which gives rise to a backtracking search. Both the efficiency of the program 
  and the solutions that are found can depend on the order in which the system tries the 
  instance. Instances that are declared last are tried first. Moreover, if instances are 
  declared in other modules, the order in which they are tried depends on the order in 
  which namespaces are opened. Instances declared in namespaces which are opened later 
  are tried earlier.

  You can change the order that type classes instances are tried by assigning them a 
  *priority*. When an instance is declared, it is assigned a priority value 
  `std.priority.default`, defined to be 1000 in module `init.core` in the standard library. 
  You can assign other priorities when defining an instance, and you can later change the 
  priority with the `attribute` command.

  (examples appear in the file `10-type_classes_Sec_10_5.lean`)"

end Sec_10_5


#print "
Section 10.6. Coercions using Type Classes
------------------------------------------

The most basic type of coercion maps elements of one type to another. For example, a 
coercion from `nat` to `int` allows us to view any element `n : nat` as an `int`. 
But some coercions depend on parameters; for example, for any type `α`, we can view 
any element `l : list α` as an element of `set α`, namely, the set of elements occurring 
in the list. The corresponding coercion is defined on the *family* of types `list α`, 
parameterized by `α`.

Lean allows us to declare three kinds of coercions:

- from a family of types to another family of types

- from a family of types to the class of sorts, which has the form

      c : Π(x₁ : A₁)...(xₙ : Aₙ), F x₁...xₙ → Type u

- from a family of types to the class of function types, which has the form

      c : Π(x₁ : A₁)...(xₙ : Aₙ), y : F x₁...xₙ,  Π(z : B), C

The first kind of coercion allows us to view any element of a member of the source family 
as an element of a corresponding member of the target family. 

The second kind allows us to view any element of a member of the source family as a type. 

The third kind allows us to view any element of the source family as a function. 

Let us consider each of these in turn.

Coercions are implemented on top of the type class resolution framework. 
We define a coercion from `α` to `β` by declaring an instance of `has_coe α β`. 

For example, we can define a coercion from `bool` to `Prop` as follows."
namespace Sec_10_6
  universe u
  def list.to_set {α : Type u} : list α → set α 
  | [] := ∅ 
  | (h::t) := {h} ∪ list.to_set t

  instance list_to_set_coe (α : Type u) : has_coe (list α) (set α) := ⟨list.to_set⟩ 

  def s : set nat := {1, 2}
  def l : list nat := [3,4]
  #check s ∪ l
  
  #print "
  Coercions are only considered if the given and expected types do not contain 
  metavariables at elaboration time. In the following example, when we elaborate the 
  union operator, the type of `[3, 2]` is `list ?m`, and a coercion will not be considered 
  since it contains metavariables."
  
  -- #check s ∪ [3,2]  (error)

  #print "We can work around this issue by using a type ascription."

  #check s ∪ [(3:nat), 2]      
  -- Alternatively,
  #check s ∪ ([3, 2]: list nat)

  -- In the examples above, you may have noticed the symbol ``↑`` produced by the 
  -- ``#check`` commands. It is the lift operator, ``↑t`` is notation for ``coe t``. 
  -- We can use this operator to force a coercion to be introduced in a particular place. 
  -- It is also helpful to make our intent clear, and work around limitations of the 
  -- coercion resolution system.

  #check s ∪ ↑[3,2] 

  variables n m : nat
  variable i : int
  #check i + ↑n + ↑m 
  #check i + ↑(nat.add n m)
  #check ↑ n + i

  #print "
  In the first two examples, the coercions are not strictly necessary since 
  Lean will insert implicit nat → int coercions. However, `#check n + i` would raise 
  an error, because the expected type of `i` is nat in order to match the type of n, 
  and no int → nat coercion exists). In the third example, we therefore insert an 
  explicit `↑` to coerce `n` to `int`. 

  The stdlib defines a coercion from subtype `{x : α // p x}` to `α` as follows:"
  instance coe_subtype { α : Type u} { p : α → Prop} : has_coe {x // p x} α := 
  ⟨λ s, subtype.val s⟩ 

  #print "
  Lean will also chain coercions as necessary. Actually, the type class `has_coe_t` is 
  the transitive closure of `has_coe`. You may have noticed that the type of `coe` 
  depends on `has_lift_t`, the transitive closure of the type class `has_lift`, 
  instead of `has_coe_t`. Every instance of `has_coe_t` is also an instance of 
  `has_lift_t`, but the elaborator only introduces automatically instances of 
  `has_coe_t`. That is, to be able to coerce using an instance of `has_lift_t`, 
  we must use the operator `↑`. In the stdlib, we have the following instance:"
  universe v
  instance lift_list {a : Type u} {b : Type v} [has_lift_t a b] :
    has_lift (list a) (list b) := ⟨ λ l, list.map (@coe a b _) l⟩
  variables s: list nat
  variables r : list int
  #check ↑s ++ r 

  #print "
  It is not an instance of `has_coe` because lists are frequently used for writing 
  programs, and we do not want a linear-time operation to be silently introduced by Lean, 
  and potentially mask mistakes performed by the user. By forcing the user to write 
  `↑`, she is making her intent clear to Lean."

  #print "
  Let us now consider the second kind of coercion. By the *class of sorts*, we mean the 
  collection `{Type u}` of universes . A coercion of the second kind is of the form
  
      c : Π(x₁ : A₁)...(xₙ : Aₙ), F x₁...xₙ → Type u

  where `F` is a family of types as above. This allows us to write `s : t` whenever `t` 
  is of type `F a₁...aₙ`. In other words, the coercion allows us to view the elements 
  of `F a₁...aₙ` as types. This is very useful when defining algebraic structures in 
  which one component, the universe of the structure, is a `Type`. For example, we can 
  define a semigroup as follows:"
  
  structure Semigroup : Type (u+1) := 
  (carrier : Type u)
  (mul : carrier → carrier → carrier)
  (mul_assoc : ∀ a b c : carrier, mul (mul a b) c = mul a (mul b c))

  instance Semigroup_has_mul (S : Semigroup) : has_mul (S.carrier) := ⟨S.mul⟩ 

  #print "
  Thus, a semigroup consists of a type, `carrier`, and an associative multiplication, `mul`.
  
  The `instance` command allows us to write `a * b` instead of `Semigroup.mul S a b` 
  whenever we have `a b : S.carrier`; notice that Lean can infer the argument `S` from the 
  types of `a` and `b`. The function `Semigroup.carrier` maps the class `Semigroup` to the 
  sort `Type u`:"

  #check Semigroup.carrier

  #print "
  If we declare this function to be a coercion, then whenever we have a semigroup 
  `S : Semigroup`, we can write `a : S` instead of `a : S.carrier`."

  instance Semigroup_to_sort : has_coe_to_sort Semigroup := {S := Type u, coe:=λ S, S.carrier}

  example (S: Semigroup) (a b c : S) : (a*b)*c = a*(b*c) := Semigroup.mul_assoc _ a b c

  #print "
  It is the coercion that makes it possible to write `(a b c : S)`. 
  
  We define an instance of `has_coe_to_sort Semigroup` instead of `has_coe Semigroup Type`. 
  The reason is that when Lean needs a coercion to sort, it only knows it needs a type, 
  but, in general, the universe is not known. The field `S` in the class `has_coe_to_sort` 
  is used to specify the universe we are coercing to.

  By the *class of function types*, we mean the collection of Pi types `Π(z : B), C`. 
  The third kind of coercion has the form
  
      c : Π(x₁ : A₁)...(xₙ : Aₙ), y : F x₁...xₙ,  Π(z : B), C

  where 
  - `F` is a family of types, 
  - `B` can depend on `x₁,...,xₙ, y`,
  - `C` can depend on on `x₁,...,xₙ, y`, and `z`

  This makes it possible to write `t s` whenever `t` has type `F a₁... aₙ`. 
  In other words, the coercion enables us to view elements of `F a₁... aₙ` as functions. 
  
  Continuing with the semigroup example, we can define the notion of a semigroup morphism. 
  That is, a function from the carrier of `S₁` to the carrier of `S₂` (note the implicit coercion) 
  that respects the multiplication. 
  
  The projection `morphism.mor` takes a morphism to the underlying function."
  
  structure morphism (S₁ S₂ : Semigroup) := 
    (mor : S₁ → S₂) 
    (resp_mul: ∀ a b : S₁, mor (a * b)  = (mor a) * (mor b))

  #check @morphism.mor

  #print "morphism is a prime candidate for the third type of coercion described above."

  instance morphism_to_fun (S₁ S₂ : Semigroup) : has_coe_to_fun (morphism S₁ S₂) :=
    { F := λ _, S₁ → S₂, coe := λ m, m.mor }

  lemma resp_mul {S₁ S₂ : Semigroup} (f: morphism S₁ S₂) (a b : S₁) : f(a * b) = f a * f b :=
    f.resp_mul a b

  --def power (S: Semigroup) : S.carrier → ℕ → S.carrier
  def power {S: Semigroup} : S → ℕ → S
    | s 0 := s
    | s (n+1) := s * (power s n)

  lemma resp_pow (S₁ S₂ : Semigroup) (f : morphism S₁ S₂) (a : S₁) (n: ℕ) :
    f(power a n) = power (f a) n := nat.rec_on n rfl
    (assume n:ℕ,
      assume ih : f(power a n) = power (f a) n,
      show f(power a (nat.succ n)) = power (f a) (nat.succ n), from 
      calc f(power a (nat.succ n)) = f(a * power a n) : rfl
                               ... = (f a) * f( power a n ) : by rw [resp_mul f]
                               ... = (f a) * power (f a) n : by rw [ih]
                               ... = power (f a) (nat.succ n) : rfl)
    

end Sec_10_6


