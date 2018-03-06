# theorem_proving

This directory collects notes that I took while working through the online book 
[Theorem Proving in Lean](https://leanprover.github.io/theorem_proving_in_lean/theorem_proving_in_lean.pdf).

## Useful commands

 `C-c C-b`, `C-c C-x`, `C-c C-r`

To execute the commands in the file `overview.lean`, load the file into emacs and then run

+ `C-c C-b` to see the results inline, or 

+ `C-c C-x` to execute the whole file

+ when hovering over a `#check` statement, the type of the expression appears in a pop-up or in the comman buffer.

+ If the `hover-over` feature is not working , then try `C-c C-r` to re-read (re-typecheck) the file.

---
	
# Theorem Proving In Lean

The remainder of this file is a collection of notes and excerpts from the tutorial [Theorem Proving in Lean](https://leanprover.github.io/documentation/).

---

## 2. Dependent Type Theory
Dependent type theory is a powerful and expressive language, allowing us to
express complex mathematical assertions, write complex hardware and software
specifications, and reason about both of these in a natural and uniform
way. Lean is based on a version of dependent type theory known as the *Calculus
of Constructions*, with a countable hierarchy of non-cumulative universes and
inductive types. Much of what this means is described below. 

---

### 2.1. Simple Type Theory

As a foundation for mathematics, set theory has a simple ontology that is rather
appealing. Everything is a set, including numbers, functions, triangles,
stochastic processes, and Riemannian manifolds.

For many purposes, including formal theorem proving, it is better to have an
infrastructure that helps manage and keep track of the various kinds of
mathematical objects we work with. "Type theory" gets its name from the fact 
that every expression has an associated *type*. For example, in a given 
context, `x + 0` may denote a natural number and `f` may denote a function
on the natural numbers. 

---
Here are some examples of how we can declare objects in Lean and check their types.
```lean
    /- declare some constants -/
    constant m : nat        -- m is a natural number
    constant n : nat
    constants b1 b2 : bool  -- declare two constants at once

    /- check their types -/
    #check m            -- output: nat
    #check n
    #check n + 0        -- nat
    #check m * (n + 0)  -- nat
    #check b1           -- bool
    #check b1 && b2     -- "&&" is boolean and
    #check b1 || b2     -- boolean or
    #check tt           -- boolean "true"
```

---

#### Comments, constants, and check

+ Any text between the `/-` and `-/` constitutes a comment that is ignored.

+ Similarly, two dashes indicate that the rest of the line contains a
  comment. Comment blocks can be nested. 

+ The `constant` and `constants` commands introduce new constant symbols into
  the working environment. 

+ The `#check` command asks Lean to report their types; commands that query
  the system for information typically begin with the hash symbol. 
  
+ Declaring new objects in this way is a good way to experiment with the system,
  but it is ultimately undesirable: Lean is a foundational system, and it
  provides us with powerful mechanisms to *define* all the mathematical objects
  we need, rather than simply postulating them. 
---

#### New Types from Old

+ What makes simple type theory powerful is that one can build new types out of
  others. For example, if `α` and `β` are types, `α → β` denotes the type
  of functions from `α` to `β`, and `α × β` denotes the cartesian product,
  that is, the type of ordered pairs consisting of an element of `α` paired
  with an element of `β`. 

```lean
    constants m n : nat
    constant f1 : nat → nat           -- type the arrow as "\to" or "\r"
    constant f2 : nat -> nat         -- alternative ASCII notation
    constant f3 : ℕ → ℕ             -- alternative notation for nat
    constant p : nat × nat           -- type the product as "\times"
    constant q : prod nat nat        -- alternative notation
    constant g1 : nat → nat → nat
    constant g2 : nat → (nat → nat)  -- has the same type as g!
    constant h : nat × nat → nat
    constant F : (nat → nat) → nat   -- a "functional"

    #check f1               -- ℕ → ℕ
    #check f1 n             -- ℕ
    #check g1 m n           -- ℕ
    #check g1 m             -- ℕ → ℕ
    #check (m, n)          -- ℕ × ℕ
    #check p.1             -- ℕ
    #check p.2             -- ℕ
    #check (m, n).1        -- ℕ
    #check (p.1, n)        -- ℕ × ℕ
    #check F f1             -- ℕ
```

---

#### Some Basic Syntax

+ The unicode arrow `→` is obtained by typing `\to` or `\r`, 
  but the ASCII alternative `->` also works; `nat -> nat` and 
  `nat → nat` mean the same thing---the type of functions from nat to nat.
+ The symbol `ℕ` is unicode notation for `nat` and is obtained by `\nat`. 
+ The symbol `×` for is obtained from `\times`. 
+ Lower-case greek letters, like `α`, `β`, and `γ`, are typically used to 
  range over types; enter them with, e.g., `\a`, `\b`, and `\g`.
+ When writing type expressions, arrows associate to the *right*; for example, the
  type of `g` is `nat → (nat → nat)`. Thus `g` is a function that takes
  natural numbers and returns another function that takes a natural number and returns a
  natural number.  This  allows us to "partially apply" the function `g`. 
+ In Lean, `(m, n)` denotes the ordered pair of `m` and `n`, and if `p`
  is a pair, `p.1` and `p.2` denote the two projections.

---

### 2.2. Types as Objects

One way in which Lean's dependent type theory extends simple type theory is that
types themselves --- entities like `nat` and `bool` --- are first-class
citizens, which is to say that they themselves are objects of study. For that to
be the case, each of them also has to have a type. 

```lean
    #check nat               -- Type
    #check bool              -- Type
    #check nat → bool        -- Type
    #check nat × bool        -- Type
    #check nat → nat         -- ...
    #check nat × nat → nat
    #check nat → nat → nat
    #check nat → (nat → nat)
    #check nat → nat → bool
    #check (nat → nat) → nat
```
We see that each one of the expressions above is an object of type `Type`. 

---

We can also declare new constants and constructors for types. 

```lean
    constants α β : Type
    constant F : Type → Type
    constant G : Type → Type → Type

    #check α        -- Type
    #check F α      -- Type
    #check F nat    -- Type
    #check G α      -- Type → Type
    #check G α β    -- Type
    #check G α nat  -- Type
```

---

We have already seen an example of a function of type 
`Type → Type → Type`, namely, the Cartesian product. 
```lean
    constants α β : Type
    #check prod α β       -- Type
    #check prod nat nat   -- Type
```
Here is another example: given any type `α`, the type `list α` denotes the
type of lists of elements of type `α`. 
```lean
    constant α : Type
    #check list α    -- Type
    #check list nat  -- Type
```

---

#### The Type of Type?

Given that every expression in Lean has a type, it is natural to ask what type
does `Type` itself have. 

```lean
    #check Type      -- Type 1
```
This reveals the first level of Lean's infinite hierarchy of types.

```lean
    #check Type     -- Type 1
    #check Type 1   -- Type 2
    #check Type 2   -- Type 3
    #check Type 3   -- Type 4
    #check Type 4   -- Type 5
```

---

#### The Hierarchy of Type Universes

+ `Type 0` is a universe of "small" or "ordinary" types; 
+ `Type 1` is a larger universe of types, which contains `Type 0` as an element; 
+ `Type 2` is a larger still universe of types, which contains `Type 1` as an element;
 
and so on... There is a `Type n` for every natural number `n`.

``Type`` is an abbreviation for `Type 0``. 

```lean
    #check Type
    #check Type 0
```

---

#### The Prop type

There is a very special type at the bottom of the hierarchy called `Prop``.
It has type `Type 0`. We will discuss `Prop`` at length below.

---

We want some operations to be *polymorphic* over type universes. For example, 
``list α`` should make sense for any type `α``, no matter which type universe
``α`` lives in. This explains the type annotation of the function `list``.

```lean
    #check list    -- Type u_1 → Type u_1
```
Here `u_1`` is a variable ranging over type levels. The output of the `#check`` 
command means whenever `α`` has type `Type n``, `list α`` also has type `Type n``. 
The function `prod`` is similarly polymorphic.

```lean
    #check prod    -- Type u_1 → Type u_2 → Type (max u_1 u_2)
```

---

#### Polymorphic constants and variables

To define polymorphic constants and variables, Lean allows us to declare universe variables explicitly.

```lean
    universe u
    constant α : Type u
    #check α
```
This is useful for giving type constructions *as much generality as possible*. 

*The ability to treat type constructors as instances of ordinary mathematical
functions is a powerful feature of dependent type theory.*

---

### 2.3. Function Abstraction and Evaluation

+ Lean recognizes $\alpha$-equivalence. (This addresses an annoying aspect 
  of Coq, where we often have to rename variables to convince the type-checker
  to unify two expressions that are clearly $\alpha$-equal.) 
+ The `#reduce` command tells Lean to evaluate an expression by reducing it to
  normal form---i.e., carry out all computational reductions sanctioned by the 
  underlying logic. 
+ In dependent type theory, every term has a computational behavior and admits a
  notion of reduction or normalization. Two terms that reduce to the same value
  are called *definitionally equal*. 
  They are considered the same by the underlying logical framework.  This is 
  one aspect of Lean that distinguishes it from other systems, like Coq or Agda.
  This aspect is sometimes refered to as "proof irrelevance."
+ The `#eval` command extracts bytecode from terms of a "computationally pure" 
  fragment of the logical framework, and can evaluate it quite efficiently.
  This contrasts with `#reduce` which relies on Lean's trusted kernel.
  As such `#reduce` is more trustworthy, but far less efficient.

---

### 2.4. Introducing Definitions

There are a number of ways to define functions in Lean.  You can use 
1. λ-abstraction,
   ```lean
   def double: ℕ → ℕ := λ x, x + x
   ```
2. λ-abstraction with some type inference,
   ```lean
   def double := λ (x : ℕ), x + x
   ```
3. or the syntax (familiar to Scala programmers),
   ```lean
   def double (x: ℕ) : ℕ := x + x
   ```
  
In the last version above, we specified the input argument and its 
type `(x: ℕ)` as well as the output type (ℕ).  The three functions 
defined above are definitionally equal.

The types of the arguments of a function can also be passed as arguments.
```lean
def compose (α β γ : Type) (g: β → γ) (f: α → β) (x: α) : γ := g (f x)
```

---

### 2.5. Local Definitions

The expression `let a := 2 in t` is *definitionally equal* to the result of 
replacing every occurrence of `a` in `t` by `2`.  For example,
```lean
def t (x : ℕ) : ℕ := let y := x + x in y * y
#reduce t 2      -- result: 16
```

---

Notice that the meaning of `let a := t1 in t2` is similar to the meaning 
of `(λ a, t2) t1`, but the two are not the same. 

In the first expression, every instance of ``a`` in ``t2`` is a syntactic 
abbreviation for ``t1``. 

In the second expression, ``a`` is a *variable*, and the expression ``λ a, t2`` 
has to make sense *independently of the value of* ``a``. 

The ``let`` construct is a stronger means of abbreviation, and there are 
expressions of the form ``let a := t1 in t2`` that cannot be expressed 
as ``(λ a, t2) t1``. 

For example, the definition of ``foo`` below type-checks, but ``bar`` does not.
	
```lean
def foo := let a := nat  in λ x : a, x + 2
/-
def bar := (λ a, λ x : a, x + 2) nat
-/
```

---

### 2.6. Variables and Sections

The ``constant`` command allows us to declare new objects, which then 
become part of the global context. 

But Lean enables us to *define* all of the mathematical objects we need, 
and *declaring* new objects willy-nilly as `constants` is lazy and dangerous. 

*Declaring a new constant is tantamount to declaring an axiomatic 
extension of our foundational system, and may result in inconsistency!*

---

We used ``constant``to create objects to work with---e.g., the types 
``α``, ``β``, and ``γ``---and to populate our context. 
This can be avoided, using implicit or explicit lambda abstraction in 
our definitions to declare such objects "locally."

```lean
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ := g (f x)
def do_twice (α : Type) (h : α → α) (x : α) : α := h (h x)
def do_thrice (α : Type) (h : α → α) (x : α) : α := h (h (h x))
```

This can be tedious, however, so Lean provides the ``variable`` and ``variables`` 
commands to make such declarations look global.

```lean
variables (α β γ : Type)
def compose (g : β → γ) (f : α → β) (x : α) : γ := g (f x)
def do_twice (h : α → α) (x : α) : α := h (h x)
def do_thrice (h : α → α) (x : α) : α := h (h (h x))
```

---

We can declare variables of any type, not just ``Type`` itself.

```lean
variables (α β γ : Type)
variables (g : β → γ) (f : α → β) (h : α → α)
variable x : α
def compose := g (f x)
def do_twice := h (h x)
def do_thrice := h (h (h x))

#print compose
#print do_twice
#print do_thrice
```

---

The ``variable(s)`` commands look like the ``constant(s)`` commands we used
above, but there is an important difference. Rather than creating permanent
entities, the former commands instruct Lean to insert the declared variables as
bound variables in definitions that refer to them. Lean is smart enough to
figure out which variables are used explicitly or implicitly in a definition. We
can therefore proceed as though ``α``, ``β``, ``γ``, ``g``, ``f``, ``h``, and
``x`` are fixed objects when we write our definitions, and let Lean abstract the
definitions for us automatically. 

Thus, a variable stays in scope until the eof, and we can't declare another
variable with the same name. Sometimes, however, it is useful to limit the scope
of a variable. For that purpose, Lean provides the notion of a ``section``.

```lean
section useful
  variables (α β γ : Type)
  variables (g : β → γ) (f : α → β) (h : α → α)
  variable x : α
  def compose := g (f x)
  def do_twice := h (h x)
  def do_thrice := h (h (h x))
end useful
```

When the section is closed, the variables go out of scope.

---

### 2.7. Namespaces

Lean provides the ability to group definitions into nested, hierarchical *namespaces*.
```lean
namespace foo
  def a : ℕ := 5
  def f (x : ℕ) : ℕ := x + 7
  def fa : ℕ := f a
  def ffa : ℕ := f (f a)
  #print "inside foo"
  #check a
  #check f
  #check fa
  #check ffa
  #check foo.fa
end foo

#print "outside the namespace"
-- #check a  -- error
-- #check f  -- error
#check foo.a
#check foo.f
#check foo.fa
#check foo.ffa
open foo
#print "opened foo"
#check a
#check f
#check fa
#check foo.fa
```

---

#### 2.7.1. The open directive

``open`` brings the shorter names into the current context. Often, when we
import a theory file, we want to open some of the namespaces it contains, to
have access to short identifiers. But sometimes we want to leave this info
hidden, for example, when they conflict with identifiers in another namespace we
want to use. Thus namespaces give us a way to manage our working environment. 

For example, Lean groups definitions and theorems involving lists into a namespace ``list``.
```lean
#check list.nil
#check list.cons
#check list.append
```
The command ``open list`` makes the shorter names available:
```lean
open list
#check nil
#check cons
#check append
```

---

Namespaces that have been closed can later be reopened, even in another file.
```lean
namespace foo
  def a : ℕ := 5
  def f (x : ℕ) : ℕ := x + 7
  def fa : ℕ := f a
end foo
#check foo.a
#check foo.f
namespace foo
  def ffa : ℕ := f (f a)
end foo
```

---

#### 2.7.2. Namespace vs. Section: similarities

In many respects, a ``namespace ... end`` block behaves like a ``section ... end`` block.

+ The scope of the ``variable`` command is limited to the current namespace.
+ The effect of the ``open`` command disappears when the current namespace is closed. 
+ Nested namespaces and sections must be closed in the order they are opened. 
+ Namespaces and sections can be nested.
```lean
namespace foo
  def a : ℕ := 5
  def f (x : ℕ) : ℕ := x + 7
  def fa : ℕ := f a
  namespace bar
   def ffa : ℕ := f (f a)
	 #check fa
	 #check ffa
  end bar
  #check fa
  #check bar.ffa
end foo
#check foo.fa
#check foo.bar.ffa
open foo
#check fa
#check bar.ffa
```

---

#### 2.7.3 Namespace vs. Section: differences

+ **Namespaces** cannot be opened within a section; they live on the *outer levels*; 
+ **Namespaces** organize data;
+ **Sections** declare variables for insertion in theorems. 

---

### 2.8. Dependent Types

An important goal in Lean is to *prove* things about the objects we define, and
below we see Lean's mechanisms for stating theorems and constructing proofs. 

For now, let us dwell on defining objects in dependent type theory. 
We will soon see what makes dependent type theory *dependent*, and why
dependent types are useful.

What makes dependent type theory dependent is that *types can depend on parameters*. 

For example, the type `list α` depends on the argument `α`,
and this dependence is what distinguishes `list ℕ` and `list bool`. 

For another example, consider the type `vec α n`, the type of vectors of
elements of `α` of length `n`.  This type depends on *two* parameters---the 
type `α : Type` of the elements in the vector, and the length `n : ℕ`. 

---

Suppose we want a function `cons` that inserts a new element at the
head of a list. What type should `cons` have? Such a function is
*polymorphic*: we expect the `cons` function for `ℕ`, `bool`, or an
arbitrary type `α` to behave the same way. So it makes sense to take the type
to be the first argument to `cons`, so that for any type, `α`, `cons α` is
the insertion function for lists of type `α`. 

It's clear that `cons α` has type `α → list α → list α`. But what type 
should `cons` have? A first guess might be 
```lean
Type → α → list α → list α
```
but, on reflection, this does not make sense: the `α` in this expression
does not refer to anything, whereas it should refer to the argument of type
`Type`. In other words, *assuming* `α : Type` is the first argument to the
function, the type of the next two elements are `α` and `list α`. These
types vary depending on the first argument, `α`. 

---

#### 2.8.1. Pi types (aka dependent function type)

```lean
Type → α → list α → list α``
```
This is an instance of a **Pi type**, or **dependent function type**. 

If `α : Type` and `β : α → Type`, then `β` is a family of types over `α`, 
that is, a type `β a` for each `a : α`. In that case, the type `Π x : α, β x`
denotes the type of functions `f` such that, if `a : α`, then `f a` is an element
of `β a`. In other words, the type of the value returned by `f` depends on its input. 

Notice that `Π x : α, β` makes sense for any expression `β : Type`. 
If the value of `β` depends on `x` (as above), then `Π x : α, β` 
denotes a dependent function type. If `β` does not depend on `x`, then 
`Π x : α, β` is no different from the type `α → β`. Indeed, in dependent
type theory (and in Lean), the Pi construction is fundamental, and `α → β` is 
just notation for `Π x : α, β` when `β` does not depend on `α`.

---

Returning to the example of lists, we can model some basic list operations as
follows (where we use `namespace hide` to avoid a naming conflict with the 
`list` type defined in the standard library.) 
```lean
namespace hide
	universe u
	constant list   : Type u → Type u
	constant cons   : Π α : Type u, α → list α → list α
	constant nil    : Π α : Type u, list α
	constant head   : Π α : Type u, list α → α
	constant tail   : Π α : Type u, list α → list α
	constant append : Π α : Type u, list α → list α → list α
end hide
```
The symbol ``Π`` can be entered by typing ``\Pi``. Here, ``nil`` is intended to
denote the empty list, ``head`` and ``tail`` return the first element of a list
and the remainder, respectively. The constant ``append`` is intended to denote
the function that concatenates two lists. 

We emphasize that these constant declarations are only for the purposes of
illustration. The ``list`` type and all these operations are, in fact, *defined*
in Lean's standard library, and are proved to have the expected properties. 

---

As the next example shows, the types described above are essentially
the types of the objects that are defined in the library. 
(The ``@`` symbol and the curly brackets will be explained momentarily.) 

```lean
open list
#check list     -- Type u_1 → Type u_1
#check @cons    -- Π {α : Type u_1}, α → list α → list α
#check @nil     -- Π {α : Type u_1}, list α
#check @head    -- Π {α : Type u_1} [_inst_1 : inhabited α], list α → α
#check @tail    -- Π {α : Type u_1}, list α → list α
#check @append  -- Π {α : Type u_1}, list α → list α → list α
```
There is a subtlety in the definition of `head`: the type `α` is required to
have at least one element, and when passed the empty list, the function must
determine a default element of the relevant type, and we see how later.

---

Vector operations are handled similarly.
```lean
universe u
constant vec : Type u → ℕ → Type u
namespace vec
  constant empty : Π α : Type u, vec α 0
  constant cons : Π (α : Type u) (n : ℕ), α → vec α n → vec α (n + 1)
  constant append : Π (α : Type u) (n m : ℕ),  vec α m → vec α n → vec α (n + m)
end vec
```

---

#### 2.8.2. Sigma types (aka dependent products)

+ A *Sigma type*, denoted `Σ x : α, β x`, is known as a *dependent product*.
  This is the type of pairs `sigma.mk a b` where `a : α` and `b : β a`.

+ Recall, the Pi type `Π x : α, β x` generalizes the notion of a function type 
  `α → β` by allowing `β` to depend on `x : α`.

+ Sigma types `Σ x : α, β x` generalize the cartesian product `α × β` in the 
  same way. In the expression `sigma.mk a b`, the type of the second element
  of the pair, `b : β a`, depends on the first element of the pair, `a : α`. 

---

```lean
variable α : Type
variable β : α → Type
variable a : α
variable b : β a

#check sigma.mk a b      -- Σ (a : α), β a
#check (sigma.mk a b).1  -- α
#check (sigma.mk a b).2  -- β (sigma.fst (sigma.mk a b))

#reduce  (sigma.mk a b).1  -- a
#reduce  (sigma.mk a b).2  -- b
```
+ `(sigma.mk a b).1` and `(sigma.mk a b).2` are short for 
  `sigma.fst (sigma.mk a b)` and `sigma.snd (sigma.mk a b)` (resp.), 
and these reduce to `a` and `b` (resp.).

---

### 2.9. Implicit Arguments

Suppose we have an implementation of lists as described above.
```lean
namespace hide
universe u
constant list : Type u → Type u
  namespace list
    constant cons   : Π α : Type u, α → list α → list α
    constant nil    : Π α : Type u, list α
    constant append : Π α : Type u, list α → list α → list α
  end list
end hide
```
Then, given a type `α`, some elements of `α`, and some lists of elements of
`α`, we can construct new lists using the constructors. 

---

```lean
namespace hide
universe u
constant list : Type u → Type u
  namespace list
    constant cons   : Π α : Type u, α → list α → list α
    constant nil    : Π α : Type u, list α
    constant append : Π α : Type u, list α → list α → list α
  end list
open hide.list
variable  α : Type
variable  a : α
variables l1 l2 : list α
#check cons α a (nil α)
#check append α (cons α a (nil α)) l1
#check append α (append α (cons α a (nil α)) l1) l2
end hide
```
+ Because the constructors are polymorphic over types, we have to insert the type
  `α` as an argument repeatedly. But this information is redundant: one can
  infer the argument `α` in `cons α a (nil α)` from the fact that the second
  argument, `a`, has type `α`. 

+ One can similarly infer the argument in `nil α`, not from anything else in
  that expression, but from the fact that it is sent as an argument to the
  function `cons`, which expects an element of type `list α` in that position. 

+ This is a central feature of dependent type theory. Terms carry a lot of
  information, and often some of that information can be inferred from the context. 

---

+ In Lean, one uses an underscore, `_`, to specify that the system
  should fill in the information automatically. This is known as an "implicit
  argument." 
```lean
namespace hide
  universe u
  constant list : Type u → Type u
  namespace list
    constant cons   : Π α : Type u, α → list α → list α
    constant nil    : Π α : Type u, list α
    constant append : Π α : Type u, list α → list α → list α
  end list
  open hide.list
  variable  α : Type
  variable  a : α
  variables l1 l2 : list α
  #check cons _ a (nil _)
  #check append _ (cons _ a (nil _)) l1
  #check append _ (append _ (cons _ a (nil _)) l1) l2
end hide
```

---

It is still tedious, however, to type all these underscores. 
When a function takes an argument that can generally be inferred from context, 
Lean allows us to specify that this argument should, by default, be left
implicit. This is done by putting the arguments in curly braces.
```lean
namespace hide
  universe u
  constant list : Type u → Type u
  namespace list
    constant cons   : Π {α : Type u}, α → list α → list α
    constant nil    : Π {α : Type u}, list α
    constant append : Π {α : Type u}, list α → list α → list α
  end list
  open hide.list
  variable  α : Type
  variable  a : α
  variables l1 l2 : list α
  #check cons a nil
  #check append (cons a nil) l1
  #check append (append (cons a nil) l1) l2
end hide
```

---

All that has changed are the braces around `α : Type u` in the declaration of
the variables. We can also use this device in function definitions.
```lean
    universe u
    def ident {α : Type u} (x : α) := x
    variables α β : Type u
    variables (a : α) (b : β)
    #check ident      -- ?M_1 → ?M_1
    #check ident a    -- α
    #check ident b    -- β
```
This makes the first argument to `ident` implicit. Notationally, this hides the specification of the type, making it look as though `ident` simply takes an argument of any type. In fact, the function `id` is defined in the standard library in exactly this way. We have chosen a nontraditional name here only to avoid a clash of names.

Variables can also be specified as implicit when they are declared with
the `variables` command:
```lean
universe u
section
  variable {α : Type u}
  variable x : α
  def ident := x
end
variables α β : Type u
variables (a : α) (b : β)
#check ident
#check ident a
#check ident b
```
This definition of `ident` here has the same effect as the one above.

---

+ Lean has complex mechanisms for instantiating implicit arguments, and they can
  be used to infer function types, predicates, and even proofs. 

+ The process of instantiating these "holes," or "placeholders," in a term
  is often known as *elaboration*. 
  
+ The presence of implicit arguments means that at times there may be
  insufficient information to fix the meaning of an expression precisely. 
  
+ An expression like `id` or `list.nil` is said to be *polymorphic*, because 
  it can take on different meanings in different contexts. 

+ One can always specify the type `T` of an expression `e` by writing `(e : T)`, 
  thereby instructing Lean's elaborator to use the value `T` as the type of `e` 
  when trying to resolve implicit arguments. 
  
---

In the second pair of examples below, the mechanism described above is used to
specify the desired types of the expressions `id` and `list.nil`. 
```lean
#check list.nil             -- list ?M1
#check id                   -- ?M1 → ?M1
#check (list.nil : list ℕ)  -- list ℕ
#check (id : ℕ → ℕ)         -- ℕ → ℕ
```
Numerals are overloaded in Lean, but when the type of a numeral cannot be
inferred, Lean assumes, by default, that it is a natural number. So the
expressions in the first two `#check` commands below are elaborated in the
same way, whereas the third `#check` command interprets `2` as an integer. 
```lean
#check 2            -- ℕ
#check (2 : ℕ)     -- ℕ
#check (2 : ℤ)      -- ℤ
```

---

Sometimes, however, we may find ourselves in a situation where we have declared
an argument to a function to be implicit, but now want to provide the argument
explicitly. If `foo` is such a function, the notation `@foo` denotes the
same function with all the arguments made explicit. 

```lean
variables α β : Type
variables (a : α) (b : β)
#check @id        -- Π {α : Type u_1}, α → α
#check @id α      -- α → α
#check @id β      -- β → β
#check @id α a    -- α
#check @id β b    -- β
```
Notice that now the first `#check` command gives the type of the identifier,
`id`, without inserting any placeholders. Moreover, the output indicates that
the first argument is implicit. 

---

### 2.10. Exercises

1. Define the function `Do_Twice`, as described
   in [Introducing Definitions](#introducing-definitions). 

2. Define the functions `curry` and `uncurry`, as described
   in [Introducing Definitions](#introducing-definitions). 

3. Above, we used the example `vec α n` for vectors of elements of type `α`
   of length `n`. Declare a constant `vec_add` that could represent a
   function that adds two vectors of natural numbers of the same length, and a
   constant `vec_reverse` that can represent a function that reverses its
   argument. Use implicit arguments for parameters that can be inferred. Declare
   some variables and check some expressions involving the constants that you
   have declared. 

4. Similarly, declare a constant `matrix` so that `matrix α m n` could
   represent the type of `m` by `n` matrices. Declare some constants to
   represent functions on this type, such as matrix addition and multiplication,
   and (using `vec`) multiplication of a matrix by a vector. Once again,
   declare some variables and check some expressions involving the constants
   that you have declared. 


--------------------------------------------------

## 3. Propositions and Proofs

### 3.1. Propositions as Types
We could introduce a new type, `Prop`, to represent propositions, and then introduce constructors to build new propositions from others.
```lean
constant and : Prop → Prop → Prop
constant or : Prop → Prop → Prop
constant not : Prop → Prop
constant implies : Prop → Prop → Prop
variables p q r : Prop
#check and p q                      -- Prop
#check or (and p q) r               -- Prop
#check implies (and p q) (and q p)  -- Prop
```

---

We could then introduce, for each `p : Prop`, another type `Proof p`, 
for the type of proofs of `p`. 
```lean
constant Proof : Prop → Type
```
An "axiom" would be constant of such a type; for example,
```lean
constant and_comm : Π (p q : Prop), Proof (implies (and p q) (and q p))
#check and_comm p q      -- Proof (implies (and p q) (and q p))
```

---

In addition to axioms, we would also need rules to build new proofs from 
old ones. For example, in many proof systems for propositional logic, we have the modus ponens rule.
```lean
constant modus_ponens (p q : Prop) : Proof (implies p q) →  Proof p → Proof q
constant modus_ponens₁ : Π (p q : Prop), Proof (implies p q) → Proof p → Proof q
#check modus_ponens p q
#check modus_ponens₁ p q
```
Systems of natural deduction for propositional logic also typically rely on 
the following rule:
```lean
constant implies_intro (p q : Prop) : (Proof p → Proof q) → Proof (implies p q).
```
This approach would provide a reasonable way of building assertions and proofs. Determining that an expression `t` is a correct proof of assertion `p` would 
then be a matter of checking that `t` has type `Proof p`. 

Some simplifications are possible:

We can avoid writing `Proof` repeatedly by conflating `Proof p` with `p` itself. 

Whenever we have `p : Prop`, we can interpret `p` as a type, namely, *the type of its proofs.* We read `t : p` as the assertion that `t` is a proof of `p`.
The rules for implication then show that we can identify `implies p q` and `p → q`.
In other words, implication `p → q` corresponds to existence of a function taking 
elements of `p` to elements of `q`. Thus the introduction of the connective `implies` 
is redundant: we can use the function space constructor `p → q` from dependent 
type theory as our notion of implication.

The rules for implication in a natural deduction system correspond to the rules 
governing *abstraction and application* for functions. This is an instance of the 
*Curry-Howard correspondence* (C-H Correspondence), or *propositions-as-types* (P-T) paradigm.

---
**Syntactic Sugar**  
+ `Prop` is alt syntax for `Sort 0`, the very bottom of the type hierarchy.  
+ `Type u` is alt syntax for `Sort (u+1)`.

---

`Prop` has some special features, but like the other type universes, it is closed 
under the arrow constructor: if `p q : Prop`, then `p → q : Prop`.

There are at least two ways of thinking about the C-H Correspondence.

**Constructive view.** 
C-H is a faithful rendering of what it means to be a proposition. 
A prop `p` is a data type that represents
*a specification of the type of data that constitutes a proof of `p`*.  
Thus, a proof `t` of `p` is simply an object of type `p`, denoted `t : p`. 

---

**Non-constructive (or classical) view.** 
C-H is a simple coding trick.
With each proposition `p` we  associate a type, which is empty if `p` is false 
and has a *single* element, say `*`, if `p` is true. In the latter case, 
we say (the type associated with) `p` is *inhabited*. 
It just so happens that the rules for function application and abstraction 
can conveniently help us keep track of which elements of `Prop` are inhabited. 
So constructing an element `t : p` tells us that `p` is indeed true. 

---

You can think of the inhabitant of `p` as being "the fact that `p` has a proof." 
(Lean document says, "the fact that `p` is true" but they're conflating "truth" 
with "has a proof".)

---

**Proof Irrelevance**   
If `p : Prop` is any prop, Lean's kernel treats any two elements `t1 t2 : p` 
as being *definitionally equal*.  This aspect of the language is known as 
**proof irrelevance**, and is consistent with the *non-constructive* 
interpretation above. It means that even though we can treat proofs 
`t : p` as ordinary objects in the language of dependent type theory, 
*they carry no information beyond the fact that `p` is true*.

---

**An Important Distinction**

+ "proofs as if people matter" or "proof relevance"  
  From the constructive point of view, proofs are *abstract mathematical objects* that 
  may be denoted (in various ways) by suitable expressions in dependent type theory. 

+ "proofs as if people don't matter" or "proof irrelevance"  
  From the non-constructive point of view, proofs are not abstract entities. 
  A syntactic expression---that we formulate using type theory in order to prove 
  a proposition---doesn't denote some abstract proof.  Rather, the expression itself
  *is* the proof. And such an expression does not denote anything beyond the fact that 
  (assuming it type-checks) the proposition in question is "true" (i.e., has a proof).

+ We may slip back and forth between these two viewpoints, at times saying that 
  an expression "constructs" or "denotes" a proof of a proposition, and at 
  other times simply saying that the expression it *is* such a proof. 


+ This is similar to the way that computer scientists occasionally blur the distinction 
  between syntax and semantics by saying, at times, that a program "computes" a certain 
  function, and at other times speaking as though the program "is" the function in question.

+ In any case, all that really matters is that the bottom line is clear. To formally express
  a mathematical assertion in the language of dependent type theory, we need to exhibit a 
  term `p : Prop`. To *prove* that assertion is to exhibit a term `t : p`. Lean's
  task, as a proof assistant, is to help us to construct such a term and to verify 
  that it is well-formed and has the correct type.

---

### 3.2. Working with Propositions as Types

In the P-T paradigm, theorems involving only `→` can be proved using lambda 
abstraction and application. 

The `theorem` command introduces a new theorem:
```lean
    constants p q : Prop
    theorem t1 : p → q → p := λ hp : p, λ hq : q, hp
```
This looks like the definition of the constant function above, only 
the arguments have type `Prop` instead of `Type`. 

The `theorem` command is a version of the `definition` command: under the C-H 
Correspondence, proving the theorem `p → q → p` is the same as defining an 
element of the associated type. To the kernel type checker, there is no difference 
between `theorem` and `definition`.
---
**Syntactic Sugar**  
+ `theorem` is alt syntax for `definition`

---
There are a few pragmatic differences between definitions and theorems. 
Under normal circumstances, it's not necessary to unfold the "definition" of 
a theorem; by proof irrelevance, any two proofs of that theorem are 
definitionally equal. 

Once the proof of a theorem is complete, typically wtnly need to know that 
the proof exists; it doesn't matter what the proof is. In light of that fact, 
Lean tags proofs as *irreducible*, which serves as a hint to the *elaborator* 
that there is generally no need to unfold it when processing a file. In fact, 
Lean is generally able to process and check proofs in parallel, since assessing 
the correctness of one proof does not require knowing the details of another.

The `#print` command will show you the proof of a theorem.
```lean
    constants p q : Prop
    theorem t1 : p → q → p := λ hp : p, λ hq : q, hp
    #print t1
```
The lambda abstractions `hp : p` and `hq : q` can be viewed as temporary 
assumptions in the proof of `t1`. 

Lean provides the alternative syntax `assume` for lambda abstractions
that denote hypotheses in a proof.  Instead of   
`theorem t1 : p → q → p := λ hp : p, λ hq : q, hp`  
we could write  
`theorem t1 : p → q → p := assume hp : p, assume hq : q, hp`

---
**Syntactic Sugar**  
+ `assume` is alt syntax for lambda abstractions that denote hypotheses in a proof.

---

We can specify the type of the final term `hp` with a `show` statement:
```lean
    constants p q : Prop
    theorem t1 : p → q → p := assume hp : p, assume hq : q,
    show p, from hp
```
Adding such extra information can improve the clarity of a proof and help 
detect errors when writing a proof. The `show` command does nothing more than 
annotate the type, and, internally, all the presentations of `t1` that we have 
seen produce the same term. 

---

Lean also allows you to use the alternative syntax `lemma` instead of theorem:
```lean
    constants p q : Prop
    lemma t1 : p → q → p :=
    assume hp : p,
    assume hq : q,
    show p, from hp
```

---

As with definitions, the lambda-abstracted variables may appear to the left 
of the colon:
```lean
    constants p q : Prop
    theorem t1 (hp : p) (hq : q) : p := hp
    #check t1    -- p → q → p
    axiom hp : p
    theorem t2 : q → p := t1 hp -- apply `t1` just as function application.
```
Declaring a `constant hp : p` is tantamount to declaring that `p` is true, 
as witnessed by `hp`.

---

Notice, by the way, that the original theorem `t1` is true for *any* propositions `p` and `q`, not just the particular constants declared. So it would be more natural to define the theorem so that it quantifies over those, too:
```lean
    theorem t1 (p q : Prop) (hp : p) (hq : q) : p := hp
    #check t1
```
The type of `t1` is now `∀ p q : Prop, p → q → p`. We can read this as the assertion "for every pair of propositions `p q`, we have `p → q → p`." The symbol `∀` is alternate syntax for `Π`, and later we will see how Pi types let us model universal quantifiers more generally. For example, we can move all parameters to the right of the colon:

---

```lean
    theorem t1 : ∀ (p q : Prop), p → q → p := 
    λ (p q : Prop) (hp : p) (hq : q), hp
```
If `p` and `q` have been declared as variables, Lean generalizes them for us.
```lean
    variables p q : Prop
    theorem t1 : p → q → p := λ (hp : p) (hq : q), hp
```
In fact, by the P-T correspondence, we can declare the assumption `hp` that `p` 
holds as another variable.
```lean
    variables p q : Prop
    variable  hp : p
    theorem t1 : q → p := λ (hq : q), hp
```
Lean detects that the proof uses `hp` and adds `hp : p` as a premise.   
In all cases, the command `#check t1` yields `∀ p q : Prop, p → q → p`. 

Remember, this type can be written `∀ (p q : Prop) (hp : p) (hq :q), p`, 
since the arrow denotes nothing more than a Pi type in which the target does not 
depend on the bound variable.

---

When we generalize `t1` this way, we can apply it to different pairs of props 
to obtain different instances of the general theorem.
```lean
    theorem t1 (p q : Prop) (hp : p) (hq : q) : p := hp
    variables p q r s : Prop
    #check t1 p q                -- p → q → p
    #check t1 r s                -- r → s → r
    #check t1 (r → s) (s → r)    -- (r → s) → (s → r) → r → s
    variable h : r → s
    #check t1 (r → s) (s → r) h  -- (s → r) → r → s
```
Once again, using the C-H Correspondence, the variable `h` of type `r → s` can 
be viewed as the hypothesis that `r → s` holds.

---

Recall the composition function discussed in the last chapter,
but with props instead of types.
```lean
    variables p q r s : Prop
    theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
    assume h₃ : p,
    show r, from h₁ (h₂ h₃)
```
As a theorem of propositional logic, what does `t2` say? 

(Numeric unicode subscripts are entered as `\0`, `\1`, `\2`, ...)

---

### 3.3. Propositional Logic

Lean defines all the standard logical connectives and notation.   
The propositional connectives come with the following notation:

| Ascii             | Unicode   | Emacs shortcut for unicode   | Definition   |
|-------------------|-----------|------------------------------|--------------|
| true              |           |                              | true         |
| false             |           |                              | false        |
| not               | ¬         | `\not`, `\neg`           | not          |
| /\\               | ∧         | `\and`                     | and          |
| \\/               | ∨         | `\or`                      | or           |
| ->                | →         | `\to`, `\r`, `\imp`    |              |
| <->               | ↔         | `\iff`, `\lr`            | iff          |

They all take values in `Prop`.

---
```lean
    variables p q : Prop
    #check p → q → p ∧ q
    #check ¬p → p ↔ false
    #check p ∨ q → q ∨ p
```
The table above indicates the order of precedence of the operations.
1. unary negation `¬` binds most strongly
2. `∧`
3. `∨`
4. `→`
5. `↔`

For example, `a ∧ b → c ∨ d ∧ e` means `(a ∧ b) → (c ∨ (d ∧ e))`. 

Remember, `→` associates to the right (nothing changes now that the 
arguments are elements of `Prop`, instead of some other `Type`), as do the 
other binary connectives. So if we have `p q r : Prop`, the expression 
`p → q → r` reads "if `p`, then if `q`, then `r`." This is just the 
"curried" form of `p ∧ q → r`.

Observe that lambda abstraction can be viewed as an "introduction rule for `→`. 
In the current setting, it shows how to "inroduce" or establish an implication. 
Application can be viewed as an "elimination rule," or implication in a proof. 
The other propositional connectives are defined in Lean's library in the file 
`init.core` (see :numref:`importing_files` for more information on the library 
hierarchy), and each connective comes with its canonical introduction and 
elimination rules.

---

#### 3.3.1. Conjunction

---

####  3.3.2. Disjunction

---

####  3.3.3. Negation and Falsity

---

#### 3.3.4. Logical Equivalence

---

### 3.4. Introducing Auxiliary Subgoals

---

### 3.5. Classical Logic

---

### 3.6. Examples of Propositional Validities

---

### 3.7. Exercises

---

---

## 4. Quantifiers and Equality

---

### The Universal Quantifier

---

### Equality

---

### Calculational Proofs

---

### The Existential Quantifier

---

### More on the Proof Language

---

### Exercises

---

---

## 5. Tactics

---

### Entering Tactic Mode

---

### Basic Tactics

---

### More Tactics

---

### Structuring Tactic Proofs

---

### Tactic Combinators

---

### Rewriting

---

### Using the Simplifier

---

### Exercises

---

## 6. Interacting with Lean

---

### Importing Files

---

### More on Sections

---

### More on Namespaces

---

### Attributes

---

### More on Implicit Arguments

---

### Notation

---

### Coercions

---

### Displaying Information

---

### Setting Options

---

### Elaboration Hints

---

### Using the Library

---


---

## 7. Inductive Types

---

### Enumerated Types

---

### Constructors with Arguments

---

### Inductively Defined Propositions

---

### Defining the Natural Numbers

---

### Other Recursive Data Types

---

### Tactics for Inductive Types

---

### Inductive Families

---

### Axiomatic Details

---

### Mutual and Nested Inductive Types

---

### Exercises

---


---

## 8. Induction and Recursion

---

### Pattern Matching

---

### Wildcards and Overlapping Patterns

---

### Structural Recursion and Induction

---

### Well-Founded Recursion and Induction

---

### Mutual Recursion

---

### Dependent Pattern Matching

---

### Inaccessible Terms

---

### Match Expressions

---

### Exercises

---

---

## 9. Structures and Records

---

### Declaring Structures

---

### Objects

---

### Inheritance

---

## 10. Type Classes

---

### Type Classes and Instances

---

### Chaining Instances

---

### Decidable Propositions

---

### Overloading with Type Classes

---

### Managing Type Class Inference

---

### Coercions using Type Classes

---


---

## 11. Axioms and Computation

---

### Historical and Philosophical Context

---

### Propositional Extensionality

---

### Function Extensionality

---

### Quotients

---

### Choice

---

### The Law of Excluded Middle

---

### Related or equivalent syntax

| pg| syntax | alternative 1   | alternative 2 | description/context/example |
| --- | ---     | ---     | ---   | ---                         |
| 8   | `assume h:p` | `λ h:p`| `fun h:p` | hypotheses in a proof |
| 11  | `#reduce`      | `#eval`  |             | `#reduce` is trustworthy; `#eval` is fast |
| 11  | `def f (x:ℕ):ℕ := x+x` | `def f:ℕ → ℕ := λ(x:ℕ), x+x` |  |  |        
| 13  | `let a := t1 in t2`    | `(λ a, t2) t1` |   | WARNING: these are NOT the same (see p.13)  |
| 16  | `namespace` | `section` |    | `namespace` organizes data, lives on outer level; `section` declares variables for insertion in theorems |
| 18  | `sigma.fst(sigma.mk a b)` | `(sigma.mk a b).fst` | `(sigma.mk a b).1` | `variable a:α`; `variable b:βa`|
| 18  | `sigma.snd (sigma.mk a b)` | `(sigma.mk a b).snd` | `(sigma.mk a b).2` | `variable a:α`; `variable b:βa`|
| 24  | `Sort (u+1)`   | `Type u` |             |                       |  
| 25, 26 | `definition`   | `theorem`| `lemma`     | but the elaborator treats these differently|
| 26  | `constant`     | `axiom`  |             |                       | 
| 26  | `∀`            | `Π`      |             | use ∀ for Props; use π for higher Types |
| 28 | `and.elim_left h` | `and.left h` | `h.left` | proves `p` when `h: p ∧ q` |
| 28 | `and.elim_right h`| `and.right h`| `h.right`| proves `q` when `h: p ∧ q` |
| 28 | `and.intro hp hq` | `⟨hp, hq⟩` |     | proves `p ∧ q` when `hp:p` and `hq:q` |
| 29 | `foo.bar e` | `e.bar` |  | `e` inhabits inductive type `foo`; `bar` a function taking `foo` args |
| 30 | `or.intro_left _ hp` | `or.inl hp`     |   | proves `p ∨ q` when `hp:p`    |
| 30 | `or.intro_right _ hq`| `or.inr hq`     |   | proves `p ∨ q` when `hq:q`    |
| 30 | `false.elim ¬p ∧ p`  | `absurd p ∧ ¬p` |   | proves `false` from `¬p ∧ p`  |
| 31 | `true.intro`         | `trivial`       |   | proves `true` from nothing    |
| 31 | `iff.elim_left h`    | `iff.mp h` | `h.mp` | proves `p → q` from `h: p ↔ q`|
| 31 | `iff.elim_right h`   | `iff.mpr h`| `h.mpr`| proves `p ← q` from `h: p ↔ q`|
| 31 | `(λ (h:p), t) s`     | `have h:p, from s, t`  |   |   |
|   |   |   |   |   |
--------------------------------------------------
