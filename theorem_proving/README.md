# Theorem Proving In Lean

This directory collects notes that I took while working through the online book
[Theorem Proving in Lean](https://leanprover.github.io/theorem_proving_in_lean/theorem_proving_in_lean.pdf).

The remainder of this file is a collection of notes and excerpts from the tutorial [Theorem Proving in Lean](https://leanprover.github.io/documentation/).

---

# 0. Some useful emacs keybindings

 `C-c C-b`, `C-c C-x`, `C-c C-r`

To execute the commands in the file `overview.lean`, load the file into emacs and then run

+ `C-c C-b` to see the results inline, or

+ `C-c C-x` to execute the whole file

+ when hovering over a `#check` statement, the type of the expression appears in a pop-up or in the comman buffer.

+ If the `hover-over` feature is not working , then try `C-c C-r` to re-read (re-typecheck) the file.

+ Numeric unicode subscripts are entered as `\0`, `\1`, `\2`, ...

---

## 1. Introduction

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

### 2.8.2. Sigma types (aka dependent products)

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

(private solutions in `src` directory)

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

We could introduce, for each `p : Prop`, another type `Proof p`,
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
**Syntactic Sugar:**  theorem <-> definition

+ `theorem` is alt syntax for `definition`

+ Under the C-H Corresp, proving the theorem `p → q → p` is the same as defining an
element of the associated type. 

+ To the kernel type checker, there is no difference between `theorem` and `definition`.

---

#### Pragmatic differences between definitions and theorems

It's typically unnecessary to unfold the "definition" of
a theorem since, by proof irrelevance, two proofs of a theorem are
definitionally equal.

Once the proof of a theorem is complete, typically we only need to know that
a proof exists. Lean tags proofs as *irreducible*, which serves as a hint
to the *elaborator* that there is generally no need to unfold it.
Consequently, Lean is can process and check proofs in parallel, since assessing
correctness of one proof does not require knowing another.

The `#print` command will show you the proof of a theorem.

```lean
  constants p q : Prop
  theorem t1 : p → q → p := λ hp : p, λ hq : q, hp
  #print t1
```
The lambda abstractions `hp : p` and `hq : q` can be viewed as temporary 
assumptions in the proof of `t1`. 

---
**Syntactic Sugar**

+ Lean provides alternative syntax `assume` for lambda abstractions
  that denote hypotheses in a proof.

+ Instead of    
  `theorem t1 : p → q → p := λ hp : p, λ hq : q, hp`  
  we could write  
  `theorem t1 : p → q → p := assume hp : p, assume hq : q, hp`

---

We can specify the type of the final term `hp` with a `show` statement:
```lean
  constants p q : Prop
  theorem t1 : p → q → p := assume hp : p, assume hq : q, show p, from hp
```
Adding such extra information can improve the clarity of a proof and help
detect errors when writing a proof. The `show` command does nothing more than
annotate the type.

---
**Syntactic Sugar**

Lean also allows you to use the alternative syntax `lemma` instead of theorem:

+ `assume` is alt syntax for lambda abstractions denoting hypotheses.

+ `lemma` is alternative syntax for `theorem`
```lean
  constants p q : Prop
  lemma t1 : p → q → p := 
    assume hp : p, assume hq : q, show p, from hp
```
---
Lambda-abstracted variables may appear to the left of the colon:
```lean
  constants p q : Prop
  theorem t1 (hp : p) (hq : q) : p := hp
  #check t1    -- p → q → p
  axiom hp : p
  theorem t2 : q → p := t1 hp -- apply `t1` just as function application.
```
`constant hp : p` is tantamount to declaring that `p` is true, as
witnessed by `hp`.

---
Notice the original theorem `t1` is true for *all* propositions `p` and `q`. 
So it's more natural to define the theorem so it quantifies over those, too:
```lean
  theorem t1 (p q : Prop) (hp : p) (hq : q) : p := hp
  #check t1
```
The type of `t1` is now `∀ p q : Prop, p → q → p`, which is the assertion 
"for every pair of propositions `p q`, we have `p → q → p`." 

---
**Syntactic Sugar**
+ `∀` is alternate syntax for `Π`
+ Later we see how Pi types model universal quantifiers more generally. 
+ For example, we can move all parameters to the right of the colon:
```lean
  theorem t1 : ∀ (p q : Prop), p → q → p :=
  λ (p q : Prop) (hp : p) (hq : q), hp
```
If `p` and `q` have been declared as variables, Lean generalizes them for us.
```lean
  variables p q : Prop
  theorem t1 : p → q → p := λ (hp : p) (hq : q), hp
```
---
In fact, by P-T correspondence, we can declare the assumption `hp` (that `p`
holds) as another variable.
```lean
  variables p q : Prop
  variable  hp : p
  theorem t1 : q → p := λ (hq : q), hp
```
Lean sees the proof uses `hp` and adds `hp : p` as a premise.
In all cases above, the command `#check t1` yields `∀ p q : Prop, p → q → p`.

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
Again, by C-H Corresp. the var `h` of type `r → s` can
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
---

### 3.3. Propositional Logic

Lean defines all the standard logical connectives and notation.   
The propositional connectives come with the following notation:

| Ascii             | Unicode   | Emacs shortcut for unicode   | Definition   |
|-------------------|-----------|------------------------------|--------------|
| true              |           |                              | true         |
| false             |           |                              | false        |
| not               | ¬         | `\not`, `\neg`               | not          |
| /\\               | ∧         | `\and`                       | and          |
| \\/               | ∨         | `\or`                        | or           |
| ->                | →         | `\to`, `\r`, `\imp`          |              |
| <->               | ↔         | `\iff`, `\lr`                | iff          |

---
Here are some examples, all of which take values in `Prop`.

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

**Example.** `a ∧ b → c ∨ d ∧ e` means `(a ∧ b) → (c ∨ (d ∧ e))`.

---

Observe that lambda abstraction can be viewed as an "introduction rule for `→`.
In the current setting, it shows how to "inroduce" or establish an implication.
Application can be viewed as an "elimination rule," or implication in a proof.
The other propositional connectives are defined in Lean's library in the file
`init.core` (see :numref:`importing_files` for more information on the library
hierarchy), and each connective comes with its canonical introduction and
elimination rules.

---

#### 3.3.1. Conjunction

**Conjunction Introduction**  
+ `and.intro h1 h2` builds a proof of `p ∧ q` using the proofs `h1 : p` and `h2 : q`.
+ `and.intro` is known as the *and-introduction rule*.

**Example.** (A proof of `p → q → p ∧ q` using `and.intro`.)
```lean
  variables p q : Prop
  theorem t3 (hp : p) (hq : q) :  p ∧ q := and.intro hp hq
  -- Alternatively:
  theorem t3' : Π (hp : p) (hq : q),  p ∧ q := λ (h₁ : p) (h₂ :q), 
    and.intro h₁ h₂
```
---

**Conjunction Elimination**
+ `example` states a theorem without naming it or storing it in the 
  permanent context. It just checks that the term has the indicated type.
+ `and.elim_left` gives a proof of `p` from a proof of `p ∧ q`.
+ `and.elim_right` gives a proof of `q` from a proof of `p ∧ q`.

The latter are known as the right and left *and-elimination rules*.

```lean  
  example (h: p ∧ q): p := and.elim_left h   -- stdlib abbrv: `and.left`
  example (h: p ∧ q): q := and.elim_right h  -- stdlib abbrv: `and.right`
```
---

**Example.** Let's prove `p ∧ q → q ∧ p`.
```lean
  theorem and_comm (h : p ∧ q) : q ∧ p := 
    and.intro (and.right h) (and.left h)
  theorem and_comm' : Π (α : Prop) (β : Prop), (α ∧ β) → (β ∧ α) :=
    λ (α β : Prop), λ (h : α ∧ β), and.intro (and.right h) (and.left h)
```
---

+ `and-introduction` and `and-elimination` are similar to the pairing and projection
  operations for the cartesian product. 
+ The difference is that given `hp : p` and `hq : q`,
   `and.intro hp hq` has type `p ∧ q : Prop`, while `pair hp hq` has type `p × q : Type`.

+ The similarity between ∧ and × is another instance of the Curry-Howard isomorphism, but
  in contrast to implication and the function space constructor,   
  *∧ and × are treated separately in Lean*.

---
**Anonymous Constructors**  
+ Certain types in Lean are structures, which is to say, the type is defined with a
single canonical constructor which builds an element of the type from a sequence of
suitable arguments. The expression `p ∧ q` is an example.

+ Lean allows us to use *anonymous constructor* notation `⟨arg1, arg2, ...⟩` in situations
  like these, when the relevant type is an inductive type and can be inferred from the
  context. In particular, we can often write ⟨hp, hq⟩ instead of and.intro hp hq.
```lean
  variables p q : Prop
  variables (hp : p) (hq : q)
  #check (⟨hp, hq⟩ : p ∧ q)        -- and.intro hp hq : p ∧ q
```
---
**Another useful syntactic gadget**
Given an expression `e` of an inductive type `fu`, the notation e.bar is 
shorthand for `fu.bar e`. Thus we can access functions without opening a 
namespace. For example, these mean the same thing.

**Examples.**
```lean
  variable l : list ℕ
  #check list.head l               -- list.head l : ℕ
  #check l.head                    -- list.head l : ℕ
```
Given `h : p ∧ q`, we can write `h.left` for `and.left h` and
`h.right` for `and.right h`.  
Thus the sample proof above can be given as follows:
```lean  
  example (h : p ∧ q) : q ∧ p := ⟨h.right, h.left⟩
```
---
#### 3.3.2. Disjunction

**Disjunction Introduction**  
+ `or.intro_left q hp` creates a proof of `p ∨ q` from a proof `hp : p`.
+ `or.intro_right p hq` creates a proof of `p ∨ q` from a proof `hq : q`.

These are called the left and right "or-introduction" rules.

**Examples.**
```lean  
  variables p q : Prop
  example (h₁ : p) : p ∨ q := or.intro_left q h₁
  example (h₂ : q) : p ∨ q := or.intro_right p h₂
```
---

**Disjunction Elimination**  
The `or-elimination` rule is slightly more complicated. The idea is that we can prove
`r` from `p ∨ q`, by showing that `r` follows from `p` and that `r` follows from `q`.  -/

In the expression `or.elim hpq hpr hqr`, the function `or.elim` takes three arguments:
  hpq : p ∨ q,     hpr : p → r,     hqr : q → r
and produces a proof of `r`.

---

Let's use `or.elim` to prove `p ∨ q → q ∨ p`.

```lean
  theorem or_comm₁ : Π (p q : Prop), p ∨ q → q ∨ p :=  
    λ (p q : Prop) (h : p ∨ q), or.elim h 
      (λ (h₁ : p), or.intro_right q h₁) 
      (λ (h₂ : q), or.intro_left p h₂)
```
We see that, using a Π type, variables p and q in advance need not be introduced above.

---

Here are two alternative versions of the last example.
(N.B. p and q must be introduced first.)

```lean  
  variables p q : Prop
  example (h : p ∨ q) : q ∨ p := or.elim h
    (assume h₁ : p, show q ∨ p, from or.intro_right q h₁)
    (assume h₂ : q, show q ∨ p, from or.intro_left p h₂)

  theorem or_comm₂ (h : p ∨ q) : q ∨ p :=
    or.elim h (λ (h₁ : p), or.inr h₁) (λ (h₂ : q), or.inl h₂)

  #check or_comm₁
  #check or_comm₂
  #print " "
```

---
**Syntactic Sugar**  
In most cases, the first argument of `or.intro_right` and `or.intro_left` 
can be inferred automatically by Lean, so it provides the following shorthands:
+ `or.inr` means `or.intro_right _`
+ `or.inl` means `or.intro_left _` 

Thus the proof term above could be written
more concisely: 
```lean
  variables p q r : Prop
  -- variables (h₁ : p) (h₂ : q)

  -- `or` has two constructors, so we can't use anonymous constructor notation.
  -- But we can still write h.elim instead of or.elim h
  theorem or_comm (h : p ∨ q) : q ∨ p :=
    h.elim (λ (h₁ : p), or.inr h₁) (λ (h₂ : q), or.inl h₂)
```

#### 3.3.3. Negation and Falsity
  
Negation, `¬p`, is defined to be `p → false`, so we obtain `¬p` by assuming
`p` and then deriving a contradiction.

Similarly, the expression `hnp hp` produces a proof of false from `hp : p`
and `hnp : ¬p`. The next example uses both these rules to produce a proof of
`(p → q) → ¬q → ¬p`.

```lean
  theorem mt (hpq : p → q) (hnq : ¬q) : ¬p :=
    assume hp : p,
    show false, from hnq (hpq hp)
  -- Alternatively, without predeclared variables,
  theorem mt₁ : Π (p q : Prop),  (p → q) → ¬q → ¬p :=
    λ (p q : Prop) (h₁: p → q) (h₂ : ¬q) (h₃ : p), h₂ (h₁ h₃)
```
---

The connective `false` has a single elimination rule, `false.elim`, which
expresses the fact that anything follows from a contradiction.

```lean
  example (h₁ : p) (h₂ : ¬p) : q := false.elim (h₂ h₁)
  example (h₁ : p) (h₂ : ¬p) : q := absurd h₁ h₂ -- notice reversal of order of hypoths
  example (h₁ : ¬p) (h₂ : q) (h₃ : q → p) : r := absurd (h₃ h₂) h₁

  -- Alternatively, without predeclared variables, these examples could
  -- be implemented using Π types and λ terms.

  theorem ex_falso₁ : Π (p q : Prop), p → ¬p → q :=
    λ (p q : Prop) (h₁ : p) (h₂ : ¬p), false.elim (h₂ h₁)
  theorem ex_falso₂ : Π (p q : Prop), p → ¬p → q :=
    λ (p q : Prop) (h₁ : p) (h₂ : ¬p), absurd h₁ h₂
  theorem absurd_example : Π (p q r : Prop), ¬p → q → (q → p) → r :=
    λ (p q r : Prop) (h₁ : ¬p) (h₂ : q) (h₃ : q → p), absurd (h₃ h₂) h₁
```

#### 3.3.4. Logical Equivalence
The expression `iff.intro h1 h2` produces a proof of `p ↔ q` from `h1 : p → q` and
`h2 : q → p`. The expression `iff.elim_left h` produces a proof of `p → q` from
`h : p ↔ q`. Similarly, `iff.elim_right h` produces a proof of `q → p` from
`h : p ↔ q`.
```lean
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
```
---
**Syntactic Sugar**
`iff.elim_left` and `iff.elim_right` represent a form of modus ponens,
so they can be abbreviated `iff.mp` and `iff.mpr`, respectively.

We can use the anonymous constructor notation to construct a proof of p ↔ q from
proofs of the forward and backward directions, and we can also use . notation with
mp and mpr.

```lean
  theorem and_swap₅ : p ∧ q ↔ q ∧ p :=
    ⟨λ (h : p ∧ q), ⟨h.right, h.left⟩, λ (h : q ∧ p), ⟨h.right, h.left⟩⟩

  example (h : p ∧ q) : q ∧ p := (and_swap₅ p q).elim_left h

  example (h : p ∧ q) : q ∧ p := (and_swap₅ p q).mp h
```

### 3.4. Introducing Auxiliary Subgoals

Another device Lean offers to help structure long proofs is the `have` 
construct, which introduces an auxiliary subgoal in a proof.

```lean
  variables p q : Prop
  theorem and_swap (h : p ∧ q) : q ∧ p :=
    have h₁ : p, from and.elim_left h,
    have h₂ : q, from and.elim_right h,
    show q ∧ p, from  and.intro h₂ h₁
  -- `show` is just for clarity; it's not required, as we see here.
  theorem and_swap₁ (h : p ∧ q) : q ∧ p :=
    have h₁ : p, from and.elim_left h,
    have h₂ : q, from and.elim_right h, and.intro h₂ h₁
```
---

Under the hood, the expression `have h : p, from s, t`
produces the term `(λ (h : p), t) s`.

In other words, `s` is a proof of `p`, `t` is a proof of the desired
conclusion assuming `h : p`, and the two are combined by lambda
astraction and application.

---

Lean also supports a structured way of reasoning backwards from a goal,
which models the "suffices to show" construction in ordinary mathematics.

```lean
  theorem and_swap₂ (h : p ∧ q) : q ∧ p :=
    have h₁ : p, from and.elim_left h,
    suffices h₂ : q, from and.intro h₂ h₁,
    show q, from and.elim_right h
```
---

### 3.5. Classical Logic

The constructive "or" is very strong: asserting p ∨ q amounts to knowing
which is the case. If RH represents the Riemann hypothesis, a classical
mathematician is willing to assert RH ∨ ¬RH, even though we cannot yet
assert either disjunct.

```lean
  open classical

  #check λ (p : Prop), em p     -- ∀ (p: Prop), p ∨ ¬p
  #check @em                    -- ∀ (p: Prop), p ∨ ¬p

  -- One consequence of LEM is the principle of double-negation elimination.
  theorem dne {p : Prop} (h : ¬¬p) : p := or.elim (em p)
      (assume h₁ : p, h₁)
      (assume h₂ : ¬p, false.elim (h h₂))
      -- alternatively,  (assume h₂ : ¬p, absurd h₂ h)

  #check @dne
```
Double-negation elimination allows one to carry out a proof by contradiction,
something which is not always possible in constructive logic.

---

**Exercise.** Prove the converse of dne, showing that em can be proved from dne.

```lean
variables p q : Prop

/- first try (didn't get this to work) -/
  -- theorem em (h : ¬¬p → p) : p ∨ ¬p :=
  --   (λ (h₃ : ¬¬p), or.inl (h h₃))
  --   (λ (h₂ : ¬p), or.inr h₂)

/- second try (still didn't get it done...but getting closer) -/
  -- theorem em (h : ¬¬p → p) : p ∨ ¬p :=
  --   show p ∨ ¬p, from
  --     suffices h₁ : ¬p ∨ ¬¬p, from or.elim h₁
  --       (assume h₂ : ¬p, or.inr h₂)
  --       (assume h₃ : ¬¬p, or.inl (h h₃)),
  --     show ¬p ∨ ¬¬p, from _
```
---
### 3.6. Examples of Propositional Validities
Lean's standard library contains proofs of many valid statements of propositional
logic, all of which you are free to use in proofs of your own. The following list
includes a number of common identities. The ones that require classical reasoning
are grouped together at the end, while the rest are constructively valid.

```lean
variables p q r s : Prop
  -- commutativity of ∧
  theorem and_comm : p ∧ q ↔ q ∧ p := iff.intro
    (assume h: p ∧ q,
      show q ∧ p, from and.intro (and.elim_right h) (and.elim_left h))
    (assume h: q ∧ p,
      show p ∧ q, from and.intro (and.elim_right h) (and.elim_left h))

  -- commutativity of ∨
  theorem or_comm : p ∨ q ↔ q ∨ p := iff.intro
    (assume h₁: p ∨ q,
      show q ∨ p, from or.elim h₁ (assume h₂ : p, or.inr h₂) (assume h₃ : q, or.inl h₃))
    (assume h₁: q ∨ p,
      show p ∨ q, from or.elim h₁ (assume h₁ : q, or.inr h₁) (assume h₂ : p, or.inl h₂))
```
---
```lean
variables p q r s : Prop
  -- associativity of ∧
  theorem and_assoc : p ∧ (q ∧ r) ↔ (p ∧ q) ∧ r := iff.intro
    (assume h : p ∧ (q ∧ r),
      show (p ∧ q) ∧ r, from and.intro (and.intro h.left h.right.left) h.right.right)
    (assume h : (p ∧ q) ∧ r,
      show p ∧ (q ∧ r), from and.intro h.left.left (and.intro h.left.right h.right))

  -- associativity of ∨
  theorem or_assoc : p ∨ (q ∨ r) ↔ (p ∨ q) ∨ r := iff.intro
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
```
---
```lean
variables p q r s : Prop
  -- distributivity of ∧ over ∨
  theorem and_dist : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := iff.intro
    (assume h : p ∧ (q ∨ r),
      have h₀ : q ∨ r, from h.right,
      show (p ∧ q) ∨ (p ∧ r), from or.elim h₀
          (assume h₁: q, or.inl (and.intro h.left h₁))
          (assume h₂: r, or.inr (and.intro h.left h₂))
    )
    (assume h : (p ∧ q) ∨ (p ∧ r),
      show p ∧ (q ∨ r), from or.elim h
        (assume h₁ : p ∧ q, and.intro h₁.left (or.inl h₁.right))
        (assume h₂ : p ∧ r, and.intro h₂.left (or.inr h₂.right))
    )

  -- distributivity of ∨ over ∧
  theorem or_distr : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := iff.intro
    (assume h : p ∨ (q ∧ r),
      show (p ∨ q) ∧ (p ∨ r), from or.elim h
        (assume h₁ : p, and.intro (or.inl h₁) (or.inl h₁))
        (assume h₂ : (q ∧ r), and.intro (or.inr h₂.left) (or.inr h₂.right))
    )
    (assume h: (p ∨ q) ∧ (p ∨ r),
      show p ∨ (q ∧ r), from
        have h₁ : p ∨ q, from h.left,
        have h₂ : p ∨ r, from h.right,
          or.elim h₁
            (assume h₃ : p, or.inl h₃)
            (assume h₄ : q,
              or.elim h₂
                (assume h₅ : p, or.inl h₅)
                (assume h₆ : r, or.inr (and.intro h₄ h₆))
            )
    )
```
---

### 3.7. Exercises
(Some solutions are in `src` directory.)
```lean
variables p q r s : Prop
variables α : Type 1
  example : (p → (q → r)) ↔ (p ∧ q → r) := iff.intro
    (assume h : p → (q → r), show (p ∧ q → r), from
      (assume h₁ : p ∧ q, show r, from
        h h₁.left h₁.right))
    (assume h : p ∧ q → r, show p → (q → r), from
      (assume (h₁ : p) (h₂ : q), show r, from
        h ⟨h₁, h₂⟩))

  -- same example again
  example : (p → (q → r)) ↔ (p ∧ q → r) := iff.intro
    ( assume h₁ : p → (q → r), show p ∧ q → r, from
        λ (h₂ : p ∧ q), h₁ h₂.left h₂.right)
    (assume h₃ : p ∧ q → r, show p → (q → r), from
        λ (h₄ : p) (h₅ : q), h₃ ⟨h₄, h₅⟩)

  -- and again
  example : (p → (q → r)) ↔ (p ∧ q → r) := iff.intro
    (assume (h₁ : p → (q → r)),
      assume (h₂ : p ∧ q),
      (h₁ h₂.left) h₂.right)
    (assume h₁ : (p ∧ q → r),
      assume (h₂ : p),
      assume h₃ : q,
      h₁ (and.intro h₂ h₃))

  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := iff.intro
    (assume h₁ : (p ∨ q) → r, show (p → r) ∧ (q → r), from
      and.intro (λ (hp : p), h₁ (or.intro_left q hp))
                (λ (hq : q), h₁ (or.intro_right p hq))
    )
    (assume h₂ : (p → r) ∧ (q → r), show (p ∨ q) → r, from
      λ (hpq: p ∨ q),
        hpq.elim (λ (hp : p), h₂.left hp) (λ (hq : q), h₂.right hq)
    )

  example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := iff.intro
    (assume h₁ : ¬(p ∨ q), show ¬p ∧ ¬q, from
    and.intro
      (assume hp : p, show false, from (h₁ (or.intro_left q hp)))
      (assume hq : q, show false, from (h₁ (or.intro_right p hq))))
      -- could also use modus tolens for this part:
      -- (mt (λ(hp : p), or.intro_left q hp) h₁)
      -- (mt (λ(hq : q), or.intro_right p hq) h₁))
    (assume h₁ : ¬p ∧ ¬q,
      assume h₂ : p ∨ q, show false, from
      or.elim h₂
        (assume (hp : p), (h₁.left hp))
        (assume (hq : q), (h₁.right hq))
      )

  example : ¬p ∨ ¬q → ¬(p ∧ q) := assume h : ¬p ∨ ¬q,
     λ(hpq : p ∧ q), show false, from
       or.elim h (assume hnp : ¬p,  hnp hpq.left) (assume hnq : ¬q,  hnq hpq.right)

  example : ¬(p ∧ ¬ p) := assume (h : p ∧ ¬p), (absurd h.left h.right)

  example : p ∧ ¬q → ¬(p → q) :=
    assume (h₁: p ∧ ¬q) (h₃: p → q), show false, from  h₁.right (h₃ h₁.left)

  example : ¬p → (p → q) := λ (h₁: ¬p) (h₂: p), false.elim (h₁ h₂)

  example : (¬p ∨ q) → (p → q) :=
    λ (h: ¬p ∨ q) (hp: p), show q, from
      or.elim h (assume hnp: ¬p, false.elim (hnp hp)) (assume hq: q, hq)

  example : p ∨ false ↔ p := iff.intro
    (assume h: p ∨ false, show p, from or.elim h
      (assume hp: p, hp) (false.elim))
    (assume hp: p, or.inl hp)

  example : p ∧ false ↔ false := iff.intro
    (assume h: p ∧ false, h.right)
    (assume h: false, ⟨false.elim h, false.elim h⟩)

  example : (p → q) → (¬q → ¬p) :=
    λ (h: p → q) (hnq: ¬q), show ¬p, from
      λ (hp: p), hnq (h hp)

  theorem lem_irrefutable (p: Prop) : ¬¬(p ∨ ¬p) :=
    assume h: ¬(p ∨ ¬p), show false, from
      suffices hnp : ¬p, from false.elim (h (or.inr hnp)),
        assume hp : p, show false, from false.elim (h (or.inl hp))

  #check lem_irrefutable

  example : ¬(p ↔ ¬p) :=
    assume h: p ↔ ¬p, show false, from
    have hr : p → ¬p, from iff.elim_left h,
    have hl : ¬p → p, from iff.elim_right h,
    suffices hneg: ¬(p ∨ ¬p), from false.elim (lem_irrefutable p hneg),
      assume hlem : p ∨ ¬p, show false, from
        or.elim hlem
          (assume hp: p, false.elim ((hr hp) hp))
          (assume hnp: ¬p, false.elim (hnp (hl hnp))
```
---
```lean
  -- these require classical reasoning
  open classical
  example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := sorry
  example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
  example : ¬(p → q) → p ∧ ¬q := sorry
  example : (p → q) → (¬p ∨ q) := sorry
  example : (¬q → ¬p) → (p → q) := sorry
  example : p ∨ ¬p := sorry
  example : (((p → q) → p) → p) := sorry
```
---
---

## 4. Quantifiers and Equality
We now extend the repertoire of logical constructions to predicates,
including the universal and existential quantifiers, and the equality relation.

---

### 4.1. The Universal Quantifier
Notice that if ``α`` is any type, we can represent a unary predicate ``p`` on ``α`` as an object of type ``α → Prop``. In that case, given ``x : α``, ``p x`` denotes the assertion that ``p`` holds of ``x``. Similarly, an object ``r : α → α → Prop`` denotes a binary relation on ``α``: given ``x y : α``, ``r x y`` denotes the assertion that ``x`` is related to ``y``.

The universal quantifier, ``∀ x : α, p x`` is supposed to denote the assertion that "for every $x$ of type $\alpha$, $p\, x$ holds." 

As before, "forall" is governed by introduction and elimination rules.

---

+ The **introduction rule for ∀** is

  - Given a proof of ``p x``, in a context where ``x : α`` is arbitrary, we obtain a proof ``∀ x : α, p x``.

+ The **elimination rule for ∀** is

  - Given a proof ``∀ x : α, p x`` and any term ``t : α``, we obtain a proof of ``p t``.

---

**The P-T interpretation.**   
Recall the **introduction rule for Pi types**:

+ Given a term ``t:β x``, in a context where ``x : α``, we have ``(λ x : α, t) : Π (x : α), β x``.

Recall the **elimination rule for Pi types**:

+ Given a term ``s : Π (x : α), β x`` and any term ``t : α``, we have ``s t : β t``.

In the case where ``p x`` has type ``Prop``, if we replace ``Π x : α, β x`` with ``∀ x : α, p x``, we can read these as the correct rules for building proofs involving the universal quantifier.

CiC identifies ``Π`` and ``∀`` in this way. 

---

**Syntactic Sugar**
If ``p`` is any expression, 

+ ``∀ (x : α), p`` is alternative notation for ``Π (x : α), p``, 

(The parentheses are unnecessary.)

The idea is that the $\forall$ notaion is more natural than the latter in cases where ``p`` is a proposition. 

Recall, in the case of function spaces, ``α → β`` is a special case of ``Π x : α, β`` in which ``β`` does not depend on ``x``. Similarly, an implication ``p → q`` between propositions is a special case of ``∀ x : p, q`` where ``q`` does not depend on ``x``.

---
**Example.** (The P-T correspondence in practice)

```lean    
  variables (α : Type) (p q : α → Prop)
  example : (∀ x : α, p x ∧ q x) → ∀ y : α, p y  :=
  assume h : ∀ x : α, p x ∧ q x,
  assume y : α,
  show p y, from (h y).left

  -- alternative version of the last example
  example : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
    λ (h : ∀ x : α, p x ∧ q x) (y : α), and.left (h y)
```
---

**Example.** (Transitivity)  
Here is how we can express the fact that a relation, ``r``, is transitive:

```lean    
  variables (α : Type) (r : α → α → Prop)
  variable trans_r : ∀ x y z : α, r x y → r y z → r x z
  variables a b c : α
  variables (h₁ : r a b) ( h₂ : r b c)
  #check trans_r                 -- ∀ (x y z : α), r x y → r y z → r x z
  #check trans_r a b c           -- r a b → r b c → r a c
  #check trans_r a b c h₁        -- r b c → r a c
  #check trans_r a b c h₁ h₂     -- r a c
```
Think about what is going on here. When we instantiate ``trans_r`` at the values ``a b c``, we end up with a proof of ``r a b → r b c → r a c``. Applying this to the "hypothesis" ``h₁ : r a b``, we get a proof of the implication ``r b c → r a c``. Finally, applying it to the hypothesis ``h₂`` yields a proof of the conclusion ``r a c``.

---

It can be tedious to supply the arguments a b c, when they can be inferred 
from hab hbc. For that reason, it is common to make these arguments implicit:

```lean
  universe u
  variables (α : Type) (r : α → α → Prop)
  variable trans_r : ∀ {x y z : α}, r x y → r y z → r x z
  variables a b c : α
  variables (h₁ : r a b) (h₂ : r b c)
  #check trans_r             -- trans_r : r ?M_1 ?M_2 → r ?M_2 ?M_3 → r ?M_1 ?M_3
  #check trans_r h₁          -- trans_r h₁ : r b ?M_1 → r a ?M_1
  #check trans_r h₁ h₂       -- trans_r h₁ h₂ : r a c
  -- The advantage is we can now write `trans_r h₁ h₂` as a proof of `r a c`.
```
---

**Example.** (elementary reasoning with equivalence relations)

```lean
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
```
---

#### Impredicativity

It is the typing rule for Pi types, and the universal quantifier in particular, 
that distinguishes Prop from other types. Suppose we have `α : Sort i` and 
`β : Sort j`, where the expression `β` may depend on a variable `x : α`. 
Then `Π x : α, β` is an element of `Type (imax i j)`, where `imax i j` is the 
maximum of `i` and `j` if `j` is not 0, and 0 otherwise.

The idea is as follows: If j is not 0, then Π x : α, β is an element of 
Sort (max i j). In other words, the type of dependent functions from α to β 
"lives" in the universe whose index is the maximum of i and j. Suppose, however,
that β is of Sort 0, that is, an element of Prop. In that case, Π x : α, β is 
an element of Sort 0 as well, no matter which type universe α lives in. 
In other words, if β is a proposition depending on α, then ∀ x : α, β is 
again a proposition. This reflects the interpretation of Prop as the type of 
propositions rather than data, and it is what makes Prop *impredicative*.

**Impredicativity of Prop.**
If `α` is a type, we can form the type `α → Prop` of all predicates on `α` (aka 
the "power type" of `α`). The impredicativity of `Prop` means that we can form 
propositions (i.e., inhabitants of Prop) that quantify over `α → Prop`. In 
particular, we can define predicates on α by quantifying over all predicates 
on α; this is the type of circularity that was once considered problematic.

---

### 4.2. Equality

Chapter 7 explains how equality is defined from primitives of Lean's 
logical framework. Here we just see how to use equality.

Of course, equality is an equivalence relation:

```lean
namespace example1
  #check eq.refl          -- ∀ (a : ?M_1), a = a
  #check eq.symm          -- ?M_2 = ?M_3 → ?M_3 = ?M_2
  #check eq.trans         -- ?M_2 = ?M_3 → ?M_3 = ?M_4 → ?M_2 = ?M_4

  -- Output is easier to read if we have Lean instantiate implicit 
  -- arguments at a particular universe u.
  universe u
  #check @eq.refl.{u}   -- ∀ {α : Sort u} (a : α), a = a
  #check @eq.symm.{u}   -- ∀ {α : Sort u} {a b : α}, a = b → b = a
  #check @eq.trans.{u}  -- ∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
end example1
```
---

**Reflexivity is more powerful than it looks.**   
Recall that the CiC treats terms with a common reduct as equal. 
As a result, some nontrivial identities can be proved by reflexivity.

```lean
namespace example2
  universe u
  variables (α β : Type u)
  example (f : α → β) (a : α) : (λ x : α, f x) a = f a := eq.refl _
  example (a₁ : α) (a₂ : α) : (a₁, a₂).1 = a₁ := eq.refl _
  example : 2 + 3 = 5 := eq.refl _

  -- This feature is so important Lean defines a notation `rfl` for `eq.refl _`.
  example (f : α → β) (a : α) : (λ x : α, f x) a = f a := rfl

end example2
```
---

**Equality is more than just an equivalence relation.**  
Equality is a congruence 
(the smallest congruence) in every congruence lattice; thus, it has the 
property that every assertion respects the equivalence.

For instance, given `h₁ : a = b` and `h₂ : p a`, we can construct a proof 
for `p b` using substitution: `eq.subst h₁ h₂`.

```lean
namespace example3
  universe u
  example (α : Type u) (a₁ a₂ : α) (p : α → Prop)
    (h₁ : a₁ = a₂) (h₂ : p a₁) : p a₂ := eq.subst h₁ h₂

-- Lean has a shorthand for eq.subst as well; it's ▸, as shown here.
  example (α : Type u) (a₁ a₂ : α) (p : α → Prop)
    (h₁ : a₁ = a₂) (h₂ : p a₁) : p a₂ := h₁ ▸ h₂
end example3
```
---

#### Substitution
`eq.subst` is used to define the following auxiliary rules, which carry out 
more explicit substitutions. They deal with applicative terms (of form s t). 
Specifically, we use `congr_arg` to replace the argument, `congr_fun` to
replace the term that is being applied, and `congr` to replace both at once.
```lean
namespace example4
  variable α : Type
  variables a₁ a₂ : α
  variables f g : α → ℕ
  variable h₁ : a₁ = a₂
  variable h₂ : f = g
  example : f a₁ = f a₂ := congr_arg f h₁
  example : f a₁ = g a₁ := congr_fun h₂ a₁
  example : f a₁ = g a₂ := congr h₂ h₁
end example4
```
---

```lean
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
```
---

Identities likes these work in arbitrary instances of the relevant 
algebraic structures, using the type class mechanism described in Chapter 10. 
Chapter 6 provides shows how to find theorems like this in the library.

```lean
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
```
---

The 2nd implicit parameter to ▸ provides the context in which the subst occurs.
This parameter has type α → Prop, so inferring this predicate requires an 
instance of *higher-order unification*.  The problem of determining whether 
a higher-order unifier exists is undecidable, and Lean can at best provide 
imperfect and approximate solutions. As a result, eq.subst doesn't always do 
what you want; this is discussed in greater detail in Section 6.10. -/

---
**IMPORTANT** (for project proposal)  
Because equational reasoning is so common and important, Lean provides a 
number of mechanisms to carry it out more effectively. The next section offers 
syntax that allow you to write calculational proofs in a more natural and 
perspicuous way. But, more importantly, equational reasoning is supported by 
a term rewriter, a simplifier, and other kinds of automation. The term rewriter 
and simplifier are described briefly in the next setion, and then in greater 
detail in the next chapter.

### 4.3. Calculational Proofs

A calculational proof (or "proof sequence") is a chain of intermediate 
results meant to be composed by basic principles such as the transitivity 
of equality. In Lean, such proofs start with the keyword `calc`, and have 
the following syntax:

           calc
             <expr>_0  'op_1'  <expr>_1  ':'  <proof>_1
             '...'   'op_2'  <expr>_2  ':'  <proof>_2
              ...
             '...'   'op_n'  <expr>_n  ':'  <proof>_n

where each `<proof>_i` is a proof for `<expr>_{i-1} op_i <expr>_i`. -/

```lean  
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
```
The style is most effective when used in conjunction with `simp` and `rewrite` 
tactics, discussed in greater detail in Ch 5.

```lean
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
```
---

### 4.4. The Existential Quantifier
Finally, consider the existential quantifier, which can be written as either 
`exists x : α, p x` or `∃ x : α, p x`. Both versions are actually abbreviations
for the expression `Exists (λ x : α, p x)`, defined in Lean's library.

As usual, the library includes both an intro and elim rule for exists. 
INTRO: to prove `∃ x : α, p x`, it suffices to provide a term `t : α` and 
a proof of `p t`.

```lean
namespace example1
  open nat
  example : ∃ x : ℕ, x > 0 := 
    have h : 1 > 0, from zero_lt_succ 0, exists.intro 1 h
  example (x : ℕ) (h : x > 0) : ∃ y : ℕ, y < x := exists.intro 0 h
  example (x y z : ℕ) (h₁ : x < y) (h₂ : y < z) : ∃ w, x < w ∧ w < z :=
    exists.intro y (and.intro h₁ h₂)
  #check @exists.intro
end example1
```
---
```lean
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
```
---

#### Witnesses and information hiding
We can view `exists.intro` as an information-hiding operation, since it hides 
the witness to the body of the assertion. 

The existential elimination rule, `exists.elim`, performs the opposite operation. 
It allows us to prove a proposition `q` from `∃ x : α, p x`, by showing that `q` follows 
from `p w` for an arbitrary value `w`. 

Roughly speaking, since we know there is some `x` satisfying `p x`, we can give it a name, 
say, `w`. If `q` does not mention `w`, then showing that `q` follows from `p w` is tantamount 
to showing that `q` follows from the existence of any such `x`.  -/

---

```lean
namespace example3
  variables (α : Type) (p q : α → Prop)
  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    exists.elim h
    (assume w,
      assume hw : p w ∧ q w,
      show ∃ x, q x ∧ p x, from ⟨w, hw.right, hw.left⟩
    )
end example3
```
**IMPORTANT.** 
The anonymous constructor notation `⟨w, hw.right, hw.left⟩` abbreviates a nested application.
Equivalently, `⟨w, ⟨hw.right, hw.left⟩⟩`.
---

It may be helpful to compare the exists-elimination rule to the or-elimination rule: 
the assertion ∃ x : α, p x can be thought of as a big disjunction of the propositions p a, 
as a ranges over all the elements of α.

An existential proposition is very similar to a sigma type (Sec 2.8). The difference is that, given 
`a : α` and `h : p a`, the term   
        `exists.intro a h` has type  `(∃ x : α, p x) : Prop`   
     whereas the term   
        `sigma.mk a h`     has type  `(Σ x : α, p x) : Type`    
     The similarity between ∃ and Σ is another instance of Curry-Howard.

```lean
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
```
---

  Next, we define `even a` as `∃ b, a = 2*b`, and then show the sum of two even numbers is even.

---

```lean
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

  -- Again, it's clearer to annotate the types.
  theorem even_plus_even' {a b : ℕ}
    (h₁ : is_even a) (h₂ : is_even b) : is_even (a + b) :=
    match h₁, h₂ with
      ⟨(w₁ : ℕ), (hw1: a = 2 * w₁)⟩, ⟨(w₂ : ℕ), (hw2 : b = 2 * w₂)⟩ := 
      ⟨w₁ + w₂, by rw [hw1, hw2, mul_add]⟩
    end
end example5  
```
---

Just as the constructive "or" is stronger than the classical "or," 
so, too, is the constructive "exists" stronger than the classical "exists". 
For example, the following implication requires classical reasoning because, 
from a constructive standpoint, knowing that it is not the case that every x 
satisfies `¬ p x` is not the same as having a particular `x` that satisfies `p x`.

```lean
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
```
---

**Exercises.**

Here are some common identities involving the existential quantifier. 
(Prove as many as you can and determine which are nonconstructive, 
and hence require some form of classical reasoning.)

```lean  
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
    (assume w, assume hpw : p w,
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
      (assume ⟨w, hpq⟩, ⟨w, or.inr hpq⟩)
  )
end constructive_examples
```
---
```lean
namespace example0
--  (∀ x, p x) ↔ ¬ (∃ x, ¬ p x)
--  NOTE: for this example, only one direction require classical axioms.
--  We split the proof up in two in order to highlight this fact. -/
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
end example0
```
---
```lean
namespace example1
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
        assume z, show p z, from dne (hcc z),
        show false, from hc hz
    )
  #check classical₁
end example1
```
---
```lean
namespace example2
-- We are asked to prove the following equivalence:  
--       (∃ x, p x) ↔ ¬ (∀ x, ¬ p x)
-- As above, we split it up to show one direction can be done constructively. -/
  variables (α :Type) (p q : α → Prop)
  variable a : α
  variable r : Prop
  theorem constructive₂ : (∃ x, p x) → ¬ (∀ x, ¬ p x) := 
    assume h : ∃ x, p x,
    assume h' : ∀ x, ¬ p x,  -- reach a contradiction (this is how we prove a negation)
    exists.elim h 
      (assume w, assume hc : p w,
        have hnc : ¬ p w, from h' w,
        show false, from hnc hc
      )
  #check constructive₂
```
---
```lean
open classical

theorem classical₂ : ¬ (∀ x, ¬ p x) → (∃ x, p x) := 
  assume h : ¬ (∀ x, ¬ p x),
  by_contradiction (
    assume h₁ : ¬ (∃ x, p x),  -- (reach a contradiction to prove `∃ x, p x`) 
    have hcc : ∀ x, ¬ p x, from
      assume w, assume h₂ : p w, -- (reach a contradiction to prove hcc)
      have h₃ : ∃ x, p x, from ⟨w, h₂⟩,
        show false, from h₁ h₃, -- (done proving hcc)
    show false, from h hcc
  )
end example2
```
---
```lean
namespace example3
-- We are asked to prove the following equivalence:  
--    (¬ ∃ x, p x) ↔ (∀ x, ¬ p x)
-- Again, we split it up to show one direction can be done without classical axioms.
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
      show false, from hwc hw
    )

  open classical
  theorem classical₃ : (¬ ∃ x, p x) → (∀ x, ¬ p x) := 
    assume h : ¬ ∃ x, p x,
    by_contradiction (
      assume hc : ¬ (∀ x, ¬ p x),
      have hcc : ∃ x, p x, from 
        example2.classical₂ α p hc,
      show false, from h hcc
    )
end example3
```
---
```lean
namespace example4
-- `(¬ ∀ x, p x) ↔ (∃ x, ¬ p x)` splits into constructive/classical directions
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
        show false, from hnw hw
      )
  open classical
  theorem classical₄ : (¬ ∀ x, p x) → (∃ x, ¬ p x) := 
    assume h : ¬ ∀ x, p x,
    by_contradiction (
      assume hn : ¬ (∃ x, ¬ p x),
      have hc : ∀ x, p x, from example1.classical₁ α p hn,        
      show false, from h hc
    )
end example4
```
---
```lean
namespace example5
-- (∀ x, p x → r) ↔ (∃ x, p x) → r
-- In this case, neither direction requires classical axioms.
  variables (α :Type) (p q : α → Prop)
  variable a : α
  variable r : Prop
  theorem constructive₅ : (∀ x, (p x → r)) ↔ (∃ x, p x) → r := iff.intro
    (assume h₁ : ∀ x, (p x → r),
      assume h₂ : ∃ x, p x,
      exists.elim h₂
      (assume w, assume hw : p w, show r, from h₁ w hw)
    )
    (assume h : (∃ x, p x) → r,
      assume w,
      assume hw : p w,
      show r, from h ⟨w, hw⟩
    )
end example5
```
---
```lean
namespace example6
-- (∃ x, p x → r) ↔ (∀ x, p x) → r
  theorem constructive₆ : (∃ x, p x → r) → (∀ x, p x) → r := 
    (assume h : ∃ x, p x → r,
      assume h' : ∀ x, p x,
      exists.elim h
      (assume w, assume hw : p w → r, show r, from hw (h' w))
    )
  theorem classical₆ : (∀ x, p x) → r → (∃ x, p x → r) :=  sorry
end example6
```
---
```lean
example : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
```    

### 4.5. More on the Proof Language

### 4.6. Exercises

(private solutions in `src` directory)

---
---

## 5. Tactics

---

### 5.1 Entering Tactic Mode

---

### 5.2 Basic Tactics

---

### 5.3 More Tactics

---

### 5.4 Structuring Tactic Proofs

---

### 5.5 Tactic Combinators

---

### 5.6 Rewriting

---

### 5.7 Using the Simplifier

---

### 5.8 Exercises

---

## 6. Interacting with Lean

In this chapter, we explore some pragmatic aspects of interacting with Lean.

---

### 6.1 Importing Files

Lean's front interprets user input, constructs formal expressions, and checks that they are well formed and type correct. 

The definitions and theorems in Lean's standard library (std lib) are spread across multiple files. Users may also wish to make use of additional libraries, or develop their own projects across multiple files. 

When Lean starts, it automatically imports the contents of the library ``init`` folder, which includes a number of fundamental definitions and constructions. As a result, most of the examples we present here work "out of the box."

---

If you want to use additional files, however, they need to be imported manually, via an ``import`` statement at the beginning of a file. 

The command
```lean
  import foo bar.baz.blah
```
imports ``foo.lean`` and ``bar/baz/blah.lean``, where the file names are given relative to the Lean *search path*. 

Information as to how the search path is determined can be found in the [documentation pages](http://leanprover.github.io/documentation/). 

---
By default, the search path includes the std lib directory, and (in some contexts) the root of the user's local project. One can also specify imports relative to the current directory.
```lean
  import .foo ..bar.baz
  -- import ``foo.lean`` from the working directory (wd)
  -- import ``bar/baz.lean`` from the parent of the wd
```
Importing is transitive. If you import ``foo`` and ``foo`` imports ``bar``, then you also have ``bar.``

----------------

### 6.2 More on Sections

Lean provides various sectioning mechanisms to help structure a theory. 

#### Variables 

Recall ([2.6. Variables and Sections](#2-6-variables-and-sections)), ``section`` allows you not only to group together elements of a theory, but also to declare variables that are inserted as arguments to theorems and definitions.

```lean
    section
      variables x y : ℕ
      def double := x + x
      #check double y
      #check double (2 * x)
      theorem t1 : double (x + y) = double x + double y := by simp [double]
      #check t1 y
      #check t1 (2 * x)
      theorem t2 : double (x * y) = double x * y := by simp [double, mul_add]
    end
```
The definition of ``double`` does not have to declare ``x`` as an argument; Lean detects the dependence and inserts it automatically. Similarly, Lean detects the occurrence of ``x`` in ``t1`` and ``t2``, and inserts it automatically there, too.

---

Note that double does *not* have ``y`` as argument. Variables are only included in declarations where they are actually mentioned. More precisely, they must be mentioned *outside of a tactic block*; because variables can appear and can be renamed dynamically in a tactic proof, there is no reliable way of determining when a name used in a tactic proof refers to an element of the context in which the theorem is parsed, and Lean does not try to guess. 

However, you can ask Lean to include a variable in every definition in a section with the ``include`` command.
```lean
    section
      variables (x y z : ℕ)
      variables (h₁ : x = y) (h₂ : y = z)
      include h₁ h₂
      theorem foo : x = z :=
      begin
        rw [h₁, h₂]
      end
      omit h₁ h₂
      theorem bar : x = z := eq.trans h₁ h₂
      theorem baz : x = x := rfl
      #check @foo
      #check @bar
      #check @baz
    end
```
The ``omit`` command simply undoes the effect of the ``include``; it does not prevent the arguments from being included automatically in subsequent theorems that mention them. 

---

The scope of the ``include`` statement can also be limited by enclosing it in a section.
```lean
    section
      variables (x y z : ℕ)
      variables (h₁ : x = y) (h₂ : y = z)
      section include_hs
      include h₁ h₂
      theorem foo : x = z :=
      begin
        rw [h₁, h₂]
      end
      end include_hs
      theorem bar : x = z := eq.trans h₁ h₂
      theorem baz : x = x := rfl
      #check @foo
      #check @bar
      #check @baz
    end
```
The include command is often useful with structures that are not mentioned explicitly but meant to be inferred by type class inference, as described in Chapter 10.

---

#### Variables: implicit and explicit
It is often the case that we want to declare section variables as explicit variables but later make them implicit, or vice-versa. One can do this with a ``variables`` command that mentions these variables with the desired brackets, without repeating the type again. Once again, sections can be used to limit scope. 

In the example below, ``x``, ``y``, and ``z`` are marked implicit in ``foo`` but explicit in ``bar``, while ``x`` is (somewhat perversely) marked as implicit in ``baz``.

```lean
    section
      variables (x y z : ℕ)
      variables (h₁ : x = y) (h₂ : y = z)
      section
        variables {x y z}
        include h₁ h₂
        theorem foo : x = z :=
        begin
          rw [h₁, h₂]
        end
      end
      theorem bar : x = z := eq.trans h₁ h₂
      variable {x}
      theorem baz : x = x := rfl
      #check @foo
      #check @bar
      #check @baz
    end
```
Using the subsequent ``variables`` commands does not change the order in which variables are inserted. It only changes the explicit/implicit annotations.

---

#### Parameters 

In fact, Lean has two ways of introducing local elements in sections: ``variables`` and ``parameters``. 

In the initial example above, the variable ``x`` is generalized immediately, so that even within the section ``double`` is a function of ``x``, and ``t1`` and ``t2`` depend explicitly on ``x``. This is what makes it possible to apply ``double`` and ``t1`` to other expressions, like ``y`` and ``2 * x``. This corresponds to the mathematical idiom "in this section, let ``x`` and ``y`` range over natural numbers."  

---

On the other hand we may wish to *fix* a value in a section.  We might say, for example, "in this section, we fix a type, ``α``, and a binary relation ``r`` on ``α``." 
The notion of a ``parameter`` captures this usage.

```lean
    section
      parameters {α : Type} (r : α → α → Type)
      parameter  transr : ∀ {x y z}, r x y → r y z → r x z
      variables {a b c d e : α}
      theorem t1 (h₁ : r a b) (h₂ : r b c) (h₃ : r c d) : r a d := 
        transr (transr h₁ h₂) h₃
      theorem t2 (h₁ : r a b) (h₂ : r b c) (h₃ : r c d) (h₄ : r d e) : r a e :=
        transr h₁ (t1 h₂ h₃ h₄)
      #check t1
      #check t2
    end
    #check t1
    #check t2
```

---

#### Parameters vs Variables
As with variables, the parameters ``α``, ``r``, and ``transr`` are inserted as arguments to definitions and theorems as needed. 

But there is a difference: within the section, ``t1`` is an abbreviation for ``@t1 α r transr``, which is to say, these arguments are held fixed until the section is closed. On the plus side, this means that you do not have to specify the explicit arguments ``r`` and ``transr`` when you write ``t1 h₂ h₃ h₄``, in contrast to the previous example. But it also means that you cannot specify other arguments in their place. 

In the example above, we would introduce $r$ as a
+ *__parameter__ if ``r`` is the only binary relation you want to reason about;*
+ *__variable__ if we want to apply the theorem to arbitrary binary relations (within the section).*

---

### 6.3 More on Namespaces

Lean provides mechanisms for working with hierarchical names.  Identifiers are given by hierarchical *names* like ``foo.bar.baz``. 

+ ``namespace foo`` causes ``foo`` to be prepended to the name of each definition and theorem until ``end foo`` is encountered. 

+ ``open foo`` then creates temporary *aliases* to definitions and theorems that begin with prefix ``foo``.

```lean
  namespace foo
    def bar : ℕ := 1
  end foo
  open foo
  #check bar
  #check foo.bar
```
---
It is not important that the definition of ``foo.bar`` was the result of a ``namespace`` command:

```lean
  def foo.bar : ℕ := 1
  open foo
  #check bar
  #check foo.bar
```

Although the names of theorems and definitions have to be unique, the aliases that identify them do not. 

For example, the std lib defines a theorem ``add_sub_cancel``, 
which asserts ``a + b - b = a`` in any additive group. 

---

The corresponding theorem on the natural numbers is named ``nat.add_sub_cancel``; it is not a special case of ``add_sub_cancel``, because the natural numbers do not form a group. 

When we open the ``nat`` namespace, the expression ``add_sub_cancel`` is overloaded, and can refer to either one. Lean tries to use type information to disambiguate the meaning in context, but you can always disambiguate by giving the full name. 

The string ``_root_`` is an explicit description of the empty prefix.
```lean
  #check add_sub_cancel
  #check nat.add_sub_cancel
  #check _root_.add_sub_cancel
````

---
#### Use protection 

To prevent overloading common names, use the ``protected`` keyword:
```lean
  namespace foo
    protected def bar : ℕ := 1
  end foo
  open foo
 -- #check bar -- (this line gives an error)
  #check foo.bar
```

This is often used for names like ``nat.rec`` and ``nat.rec_on`` (to prevent overloading).

---

#### The open command

The ``open`` command admits variations. 
+ The following creates aliases for only the identifiers listed:
  ```lean
    open nat (succ add sub)
  ```
+ The following creates aliases for everything in the ``nat`` namespace *except* the identifiers listed:
  ```lean
    open nat (hiding succ add sub)
  ```
+ This creates aliases for everything in ``nat`` except ``succ`` and ``sub``, renaming ``nat.add`` to ``plus``, and renaming the protected definition ``nat.induction_on`` to ``induction_on``.
  ```lean
    open nat (renaming mul → times) (renaming add → plus) (hiding succ sub)
  ```
---

#### Transfering aliases to other namespaces

It is sometimes useful to ``export`` aliases from one namespace to another, or to the top level. 

The following creates aliases for ``succ``, ``add``, and ``sub`` in the current namespace, so that whenever the namespace is open, these aliases are available. 
```lean
    export nat (succ add sub)
```
If this command is used outside a namespace, the aliases are exported to the top level. The ``export`` command admits all the variations described above.

---

### 6.4 Attributes

The main function of Lean is to translate user input to formal expressions that are checked by the kernel for correctness and then stored in the environment for later use. 

But some commands have other effects on the environment, either assigning attributes to objects in the environment, defining notation, or declaring instances of *type classes* (Chapter 10).

Most of these commands have global effects, which is to say, that they remain in effect not only in the current file, but also in any file that imports it. 

Often such commands be prefixed with the ``local`` modifier, indicating that they are in effect only until the current ``section`` or ``namespace`` is closed, or until the end of the current file.

---

Above we saw that theorems can be annotated with the ``[simp]`` attribute, which makes them available for use by the simplifier. The following example... 
1. ...defines divisibility on `nat`;
2. ...makes `nat` an *instance* (Chapter 10) of a type for which the divisible notation ``\|`` is available;
3. ...assigns the ``[simp]`` attribute.

```lean
  def nat.dvd (m n : ℕ) : Prop := ∃ k, n = m * k
  instance : has_dvd nat := ⟨nat.dvd⟩
  attribute [simp]
  theorem nat.dvd_refl (n : ℕ) : n ∣ n := (1, by simp)
  example : 5 ∣ 5 := by simp
```
Here the simplifier proves ``5 ∣ 5`` by rewriting it to ``true``. 

---

Lean allows the alternative annotation ``@[simp]`` before a theorem to assign the attribute.
```lean
  def nat.dvd (m n : ℕ) : Prop := ∃ k, n = m * k
  instance : has_dvd nat := ⟨nat.dvd⟩
  @[simp]
  theorem nat.dvd_refl (n : ℕ) : n ∣ n := ⟨1, by simp⟩
````
One can also assign the attribute any time after the definition takes place:
```lean
    def nat.dvd (m n : ℕ) : Prop := ∃ k, n = m * k
    instance : has_dvd nat := ⟨nat.dvd⟩
    theorem nat.dvd_refl (n : ℕ) : n ∣ n := ⟨1, by simp⟩
    attribute [simp] nat.dvd_refl
```
In all these cases, the attribute remains in effect in any file that imports the one in which the declaration occurs. 

---
#### The `local` modifier

Adding the ``local`` modifier restricts the scope. For example,

```lean
  def nat.dvd (m n : ℕ) : Prop := ∃ k, n = m * k
  instance : has_dvd nat := ⟨nat.dvd⟩
  -- BEGIN
  section
  local attribute [simp]
  theorem nat.dvd_refl (n : ℕ) : n ∣ n := ⟨1, by simp⟩
  example : 5 ∣ 5 := by simp
  end
  -- error:
  -- example : 5 ∣ 5 := by simp
  -- END
```
In fact, the ``instance`` command works by automatically generating a theorem name and assigning an ``[instance]`` attribute to it. The declaration can also be made local:
```lean
  def nat.dvd (m n : ℕ) : Prop := ∃ k, n = m * k
  section
  def has_dvd_nat : has_dvd nat := ⟨nat.dvd⟩
  local attribute [instance] has_dvd_nat
  local attribute [simp]
  theorem nat.dvd_refl (n : ℕ) : n ∣ n := ⟨1, by simp⟩
  example : 5 ∣ 5 := by simp
  end
  -- error: 
  -- #check 5 ∣ 5
```
---
Here's another example. The ``reflexivity`` tactic makes use of objects in the environment that have been tagged with the ``[refl]`` attribute.
```lean
  def nat.dvd (m n : ℕ) : Prop := ∃ k, n = m * k
  instance has_dvd_nat : has_dvd nat := ⟨nat.dvd⟩
  @[simp,refl]
  theorem nat.dvd_refl (n : ℕ) : n ∣ n := ⟨1, by simp⟩
  example : 5 ∣ 5 := by reflexivity
```
The scope of the ``[refl]`` attribute can similarly be restricted using the ``local`` modifier, as above.

---

In the section on Notation below, we will discuss Lean's mechanisms for defining notation, and see that they also support the ``local`` modifier. However, in Section [6.9: Setting Options](#6-9-setting-options), we show how to set options, which does *not* follow this pattern: options can *only* be set locally, which is to say, their scope is always restricted to the current section or current file.

---

### 6.5 More on Implicit Arguments

Above we saw that if the term ``t`` has type ``Π {x : α}, β x``, then the curly brackets indicate that ``x`` has been marked as an *implicit argument* to ``t``. This means that whenever you write ``t``, a placeholder, or "hole," is inserted, so that ``t`` is replaced by ``@t _``. If you don't want that to happen, you have to write ``@t`` instead.

Notice that implicit arguments are inserted eagerly. Suppose we define a function ``f (x : ℕ) {y : ℕ} (z : ℕ)`` with the arguments shown. Then, when we write the expression ``f 7`` without further arguments, it is parsed as ``f 7 _``. Lean offers a weaker annotation, ``{{y : ℕ}}``, which specifies that a placeholder should only be added *before* a subsequent explicit argument. This annotation can also be written using as ``⦃y : ℕ⦄``, where the unicode brackets are entered as ``\{{`` and ``\}}``, respectively. With this annotation, the expression ``f 7`` would be parsed as is, whereas ``f 7 3`` would be parsed as ``f 7 _ 3``, just as it would be with the strong annotation.

To illustrate the difference, consider the following example, which shows that a reflexive euclidean relation is both symmetric and transitive.

```lean
    namespace hide
    -- BEGIN
    variables {α : Type} (r : α → α → Prop)
    definition reflexive  : Prop := ∀ (a : α), r a a
    definition symmetric  : Prop := ∀ {a b : α}, r a b → r b a
    definition transitive : Prop := ∀ {a b c : α}, r a b → r b c → r a c
    definition euclidean  : Prop := ∀ {a b c : α}, r a b → r a c → r b c
    variable {r}
    theorem th1 (reflr : reflexive r) (euclr : euclidean r) : symmetric r := 
      assume a b : α, assume : r a b,
	  show r b a, from euclr this (reflr _)
    theorem th2 (symmr : symmetric r) (euclr : euclidean r) : 
      transitive r := assume (a b c : α), assume (rab : r a b) (rbc : r b c),
      euclr (symmr rab) rbc
    -- error:
    -- theorem th3 (reflr: reflexive r) (euclr: euclidean r) : transitive r := 
		 th2 (th1 reflr euclr) euclr
    theorem th3 (reflr : reflexive r) (euclr : euclidean r) : 
      transitive r := @th2 _ _ (@th1 _ _ reflr @euclr) @euclr
    -- END
    end hide
```

The results are broken down into small steps: ``th1`` shows that a relation that is reflexive and euclidean is symmetric, and ``th2`` shows that a relation that is symmetric and euclidean is transitive. Then ``th3`` combines the two results. But notice that we have to manually disable the implicit arguments in ``th1``, ``th2``, and ``euclr``, because otherwise too many implicit arguments are inserted. The problem goes away if we use weak implicit arguments:

```lean
    namespace hide
    -- BEGIN
    variables {α : Type} (r : α → α → Prop)
    definition reflexive  : Prop := ∀ (a : α), r a a
    definition symmetric  : Prop := ∀ ⦃a b : α⦄, r a b → r b a
    definition transitive : Prop := ∀ ⦃a b c : α⦄, r a b → r b c → r a c
    definition euclidean  : Prop := ∀ ⦃a b c : α⦄, r a b → r a c → r b c
    variable {r}  
    theorem th1 (reflr : reflexive r) (euclr : euclidean r) : symmetric r :=
      assume a b : α, assume : r a b,
      show r b a, from euclr this (reflr _)
    theorem th2 (symmr : symmetric r) (euclr : euclidean r) : transitive r :=
      assume (a b c : α), assume (rab : r a b) (rbc : r b c), euclr (symmr rab) rbc
    theorem th3 (reflr : reflexive r) (euclr : euclidean r) : transitive r :=
      th2 (th1 reflr euclr) euclr
    -- END
    end hide
```

There is a third kind of implicit argument that is denoted with square brackets, ``[`` and ``]``. These are used for type classes, as explained in :numref:`Chapter %s <type_classes>`.

---

### 6.6 Notation

Identifiers in Lean can include any alphanumeric characters, including Greek characters (other than Π , Σ , and λ , which, as we have seen, have a special meaning in the dependent type theory). They can also include subscripts, which can be entered by typing ``\_`` followed by the desired subscripted character.

Lean's parser is extensible, which is to say, we can define new notation.

```lean

    notation `[` a `**` b `]` := a * b + 1

    def mul_square (a b : ℕ) := a * a * b * b

    infix `<*>`:50 := mul_square

    #reduce [2 ** 3]
    #reduce 2 <*> 3
```
In this example, the ``notation`` command defines a complex binary notation for multiplying and adding one. The ``infix`` command declares a new infix operator, with precedence 50, which associates to the left. (More precisely, the token is given left-binding power 50.) The command ``infixr`` defines notation which associates to the right, instead.

If you declare these notations in a namespace, the notation is only available when the namespace is open. You can declare temporary notation using the keyword ``local``, in which case the notation is available in the current file, and moreover, within the scope of the current ``namespace`` or ``section``, if you are in one.

```lean

    local notation `[` a `**` b `]` := a * b + 1
    local infix `<*>`:50 := λ a b : ℕ, a * a * b * b
```

Lean's core library declares the left-binding powers of a number of common symbols.

    https://github.com/leanprover/lean/blob/master/library/init/core.lean

You are welcome to overload these symbols for your own use, but you cannot change their binding power.

You can direct the pretty-printer to suppress notation with the command ``set_option pp.notation false``. You can also declare notation to be used for input purposes only with the ``[parsing_only]`` attribute:

```lean

    notation [parsing_only] `[` a `**` b `]` := a * b + 1

    variables a b : ℕ
    #check [a ** b]
```

The output of the ``#check`` command displays the expression as ``a * b + 1``. Lean also provides mechanisms for iterated notation, such as ``[a, b, c, d, e]`` to denote a list with the indicated elements. See the discussion of ``list`` in the next chapter for an example.

The possibility of declaring parameters in a section also makes it possible to define local notation that depends on those parameters. In the example below, as long as the parameter ``m`` is fixed, we can write ``a ≡ b`` for equivalence modulo ``m``. As soon as the section is closed, however, the dependence on ``m`` becomes explicit, and the notation ``a ≡ b`` is no longer valid.

```lean

    namespace int

    def dvd (m n : ℤ) : Prop := ∃ k, n = m * k
    instance : has_dvd int := ⟨int.dvd⟩

    @[simp]
    theorem dvd_zero (n : ℤ) : n ∣ 0 :=
    ⟨0, by simp⟩

    theorem dvd_intro {m n : ℤ} (k : ℤ) (h : n = m * k) : m ∣ n :=
    ⟨k, h⟩

    end int

    open int

    -- BEGIN
    section mod_m
      parameter (m : ℤ)
      variables (a b c : ℤ)

      definition mod_equiv := (m ∣ b - a)

      local infix ≡ := mod_equiv

      theorem mod_refl : a ≡ a :=
      show m ∣ a - a, by simp

      theorem mod_symm (h : a ≡ b) : b ≡ a :=
      by cases h with c hc; apply dvd_intro (-c); simp [eq.symm hc]

      theorem mod_trans (h₁ : a ≡ b) (h₂ : b ≡ c) : a ≡ c :=
      begin
        cases h₁ with d hd, cases h₂ with e he, 
        apply dvd_intro (d + e),
        simp [mul_add, eq.symm hd, eq.symm he]
      end
    end mod_m

    #check (mod_refl : ∀ (m a : ℤ), mod_equiv m a a)

    #check (mod_symm : ∀ (m a b : ℤ), mod_equiv m a b → 
                         mod_equiv m b a)

    #check (mod_trans :  ∀ (m a b c : ℤ), mod_equiv m a b → 
                           mod_equiv m b c → mod_equiv m a c)
    -- END
```

Coercions
---------

In Lean, the type of natural numbers, ``nat``, is different from the type of integers, ``int``. But there is a function ``int.of_nat`` that embeds the natural numbers in the integers, meaning that we can view any natural numbers as an integer, when needed. Lean has mechanisms to detect and insert *coercions* of this sort.

```lean
    variables m n : ℕ
    variables i j : ℤ

    #check i + m      -- i + ↑m : ℤ
    #check i + m + j  -- i + ↑m + j : ℤ
    #check i + m + n  -- i + ↑m + ↑n : ℤ
```

Notice that the output of the ``#check`` command shows that a coercion has been inserted by printing an arrow. The latter is notation for the function ``coe``; you can type the unicode arrow with ``\u`` or use the ``coe`` instead. In fact, when the order of arguments is different, you have to insert the coercion manually, because Lean does not recognize the need for a coercion until it has already parsed the earlier arguments.

```lean
    variables m n : ℕ
    variables i j : ℤ

    -- BEGIN
    #check ↑m + i        -- ↑m + i : ℤ
    #check ↑(m + n) + i  -- ↑(m + n) + i : ℤ
    #check ↑m + ↑n + i   -- ↑m + ↑n + i : ℤ
    -- END
```

In fact, Lean allows various kinds of coercions using type classes; for details, see :numref:`coercions_using_type_classes`.

Displaying Information
----------------------

There are a number of ways in which you can query Lean for information about its current state and the objects and theorems that are available in the current context. You have already seen two of the most common ones, ``#check`` and ``#reduce``. Remember that ``#check`` is often used in conjunction with the ``@`` operator, which makes all of the arguments to a theorem or definition explicit. In addition, you can use the ``#print`` command to get information about any identifier. If the identifier denotes a definition or theorem, Lean prints the type of the symbol, and its definition. If it is a constant or an axiom, Lean indicates that fact, and shows the type.

```lean
    -- examples with equality
    #check eq
    #check @eq
    #check eq.symm
    #check @eq.symm

    #print eq.symm

    -- examples with and
    #check and
    #check and.intro
    #check @and.intro

    -- a user-defined function
    def foo {α : Type} (x : α) : α := x

    #check foo
    #check @foo
    #reduce foo
    #reduce (foo nat.zero)
    #print foo

There are other useful ``#print`` commands:

.. code-block:: text

    #print definition             : display definition
    #print inductive              : display an inductive type and its constructors
    #print notation               : display all notation
    #print notation <tokens>      : display notation using any of the tokens
    #print axioms                 : display assumed axioms
    #print options                : display options set by user
    #print prefix <namespace>     : display all declarations in the namespace
    #print classes                : display all classes
    #print instances <class name> : display all instances of the given class
    #print fields <structure>     : display all fields of a structure
```

We will discuss inductive types, structures, classes, instances in the next four chapters. Here are examples of how these commands are used:

```lean
    #print notation
    #print notation + * -
    #print axioms
    #print options
    #print prefix nat
    #print prefix nat.le
    #print classes
    #print instances ring
    #print fields ring
```

The behavior of the generic print command is determined by its argument, so that the following pairs of commands all do the same thing.

```lean
    #print list.append
    #print definition list.append

    #print +
    #print notation +

    #print nat
    #print inductive nat

    #print group
    #print inductive group
```

Moreover, both ``#print group`` and ``#print inductive group`` recognize that a group is a structure (see :numref:`Chapter %s <structures_and_records>`), and so print the fields as well.

.. _setting_options:

Setting Options
---------------

Lean maintains a number of internal variables that can be set by users to control its behavior. The syntax for doing so is as follows:


```lean
    set_option <name> <value>
```

One very useful family of options controls the way Lean's *pretty- printer* displays terms. The following options take an input of true or false:

```lean
    pp.implicit  : display implicit arguments
    pp.universes : display hidden universe parameters
    pp.coercions : show coercions
    pp.notation  : display output using defined notations
    pp.beta      : beta reduce terms before displaying them
```

As an example, the following settings yield much longer output:

```lean

    set_option pp.implicit true
    set_option pp.universes true
    set_option pp.notation false
    set_option pp.numerals false

    #check 2 + 2 = 4
    #reduce (λ x, x + 2) = (λ x, x + 3)
    #check (λ x, x + 1) 1
```

The command ``set_option pp.all true`` carries out these settings all at once, whereas ``set_option pp.all false`` reverts to the previous values. Pretty printing additional information is often very useful when you are debugging a proof, or trying to understand a cryptic error message. Too much information can be overwhelming, though, and Lean's defaults are generally sufficient for ordinary interactions.

By default, the pretty-printer does not reduce applied lambda-expressions, but this is sometimes useful. The ``pp.beta`` option controls this feature.

```lean

    set_option pp.beta true
    #check (λ x, x + 1) 1
```

.. _elaboration_hints:

Elaboration Hints
-----------------

When you ask Lean to process an expression like ``λ x y z, f (x + y) z``, you are leaving information implicit. For example, the types of ``x``, ``y``, and ``z`` have to be inferred from the context, the notation ``+`` may be overloaded, and there may be implicit arguments to ``f`` that need to be filled in as well. Moreover, we will see in :numref:`Chapter %s <type_classes>` that some implicit arguments are synthesized by a process known as *type class resolution*. And we have also already seen in the last chapter that some parts of an expression can be constructed by the tactic framework.

Inferring some implicit arguments is straightforward. For example, suppose a function ``f`` has type ``Π {α : Type}, α → α → α`` and Lean is trying to parse the expression ``f n``, where ``n`` can be inferred to have type ``nat``. Then it is clear that the implicit argument ``α`` has to be ``nat``. However, some inference problems are *higher order*. For example, the substitution operation for equality, ``eq.subst``, has the following type:

.. code-block:: text

    eq.subst : ∀ {α : Sort u} {p : α → Prop} {a b : α}, 
                 a = b → p a → p b

Now suppose we are given ``a b : ℕ`` and ``h₁ : a = b`` and ``h₂ : a * b > a``. Then, in the expression ``eq.subst h₁ h₂``, ``P`` could be any of the following:

-  ``λ x, x * b > x``
-  ``λ x, x * b > a``
-  ``λ x, a * b > x``
-  ``λ x, a * b > a``

In other words, our intent may be to replace either the first or second ``a`` in ``h₂``, or both, or neither. Similar ambiguities arise in inferring induction predicates, or inferring function arguments. Even second-order unification is known to be undecidable. Lean therefore relies on heuristics to fill in such arguments, and when it fails to guess the right ones, they need to be provided explicitly.

To make matters worse, sometimes definitions need to be unfolded, and sometimes expressions need to be reduced according to the computational rules of the underlying logical framework. Once again, Lean has to rely on heuristics to determine what to unfold or reduce, and when.

There are attributes, however, that can be used to provide hints to the elaborator. One class of attributes determines how eagerly definitions are unfolded: constants can be marked with the attribute ``[reducible]``, ``[semireducible]``, or ``[irreducible]``. Definitions are marked ``[semireducible]`` by default. A definition with the ``[reducible]`` attribute is unfolded eagerly; if you think of a definition are serving as an abbreviation, this attribute would be appropriate. The elaborator avoids unfolding definitions with the ``[irreducible]`` attribute. Theorems are marked ``[irreducible]`` by default, because typically proofs are not relevant to the elaboration process.

It is worth emphasizing that these attributes are only hints to the elaborator. When checking an elaborated term for correctness, Lean's kernel will unfold whatever definitions it needs to unfold. As with other attributes, the ones above can be assigned with the ``local`` modifier, so that they are in effect only in the current section or file.

Lean also has a family of attributes that control the elaboration strategy. A definition or theorem can be marked ``[elab_with_expected_type]``, ``[elab_simple]``. or ``[elab_as_eliminator]``. When applied to a definition ``f``, these bear on elaboration of an expression ``f a b c ...`` in which ``f`` is applied to arguments. With the default attribute, ``[elab_with_expected_type]``, the arguments ``a``, ``b``, ``c``, ... are elaborating using information about their expected type, inferred from ``f`` and the previous arguments. In contrast, with ``[elab_simple]``, the arguments are elaborated from left to right without propagating information about their types. The last attribute, ``[elab_as_eliminator]``, is commonly used for eliminators like recursors, induction principles, and ``eq.subst``. It uses a separate heuristic to infer higher-order parameters. We will consider such operations in more detail in the next chapter.

Once again, these attributes can assigned and reassigned after an object is defined, and you can use the ``local`` modifier to limit their scope. Moreover, using the ``@`` symbol in front of an identifier in an expression instructs the elaborator to use the ``[elab_simple]`` strategy; the idea is that, when you provide the tricky parameters explicitly, you want the elaborator to weigh that information heavily. In fact, Lean offers an alternative annotation, ``@@``, which leaves parameters before the first higher-order parameter explicit. For example, ``@@eq.subst`` leaves the type of the equation implicit, but makes the context of the substitution explicit.

Using the Library
-----------------

To use Lean effectively you will inevitably need to make use of definitions and theorems in the library. Recall that the ``import`` command at the beginning of a file imports previously compiled results from other files, and that importing is transitive; if you import ``foo`` and ``foo`` imports ``bar``, then the definitions and theorems from ``bar`` are available to you as well. But the act of opening a namespace, which provides shorter names, does not carry over. In each file, you need to open the namespaces you wish to use.

In general, it is important for you to be familiar with the library and its contents, so you know what theorems, definitions, notations, and resources are available to you. Below we will see that Lean's editor modes can also help you find things you need, but studying the contents of the library directly is often unavoidable. Lean's standard library can be found online, on github:

    https://github.com/leanprover/lean/tree/master/library

You can see the contents of the directories and files using github's browser interface. If you have installed Lean on your own computer, you can find the library in the ``lean`` folder, and explore it with your file manager. Comment headers at the top of each file provide additional information.

Lean's library developers follow general naming guidelines to make it easier to guess the name of a theorem you need, or to find it using tab completion in editors with a Lean mode that supports this, which is discussed in the next section. Identifiers are generally ``snake_case``, which is to say, they are composed of words written in lower case separated by underscores. For the most part, we rely on descriptive names. Often the name of theorem simply describes the conclusion:

```lean
    open nat
    #check succ_ne_zero
    #check @mul_zero
    #check @mul_one
    #check @sub_add_eq_add_sub
    #check @le_iff_lt_or_eq
```

If only a prefix of the description is enough to convey the meaning, the name may be made even shorter:

```lean
    open nat
    -- BEGIN
    #check @neg_neg
    #check pred_succ
    -- END
```

Sometimes, to disambiguate the name of theorem or better convey the intended reference, it is necessary to describe some of the hypotheses. The word "of" is used to separate these hypotheses:

```lean
    #check @nat.lt_of_succ_le
    #check @lt_of_not_ge
    #check @lt_of_le_of_ne
    #check @add_lt_add_of_lt_of_le
```

Sometimes the word "left" or "right" is helpful to describe variants of a theorem.

```lean
    #check @add_le_add_left
    #check @add_le_add_right
```

We can also use the word "self" to indicate a repeated argument:

```lean
    #check mul_inv_self
    #check neg_add_self
```

Remember that identifiers in Lean can be organized into hierarchical namespaces. For example, the theorem named ``lt_of_succ_le`` in the namespace ``nat`` has full name ``nat.lt_of_succ_le``, but the shorter name is made available by the command ``open nat``. We will see in :numref:`Chapter %s <inductive_types>` and :numref:`Chapter %s <structures_and_records>` that defining structures and inductive data types in Lean generates associated operations, and these are stored in a namespace with the same name as the type under definition. For example, the product type comes with the following operations:

```lean
    #check @prod.mk
    #check @prod.fst
    #check @prod.snd
    #check @prod.rec
```

The first is used to construct a pair, whereas the next two, ``prod.fst`` and ``prod.snd``, project the two elements. The last, ``prod.rec``, provides another mechanism for defining functions on a product in terms of a function on the two components. Names like ``prod.rec`` are *protected*, which means that one has to use the full name even when the ``prod`` namespace is open.

With the propositions as types correspondence, logical connectives are also instances of inductive types, and so we tend to use dot notation for them as well:

```lean
    #check @and.intro
    #check @and.elim
    #check @and.left
    #check @and.right
    #check @or.inl
    #check @or.inr
    #check @or.elim
    #check @exists.intro
    #check @exists.elim
    #check @eq.refl
    #check @eq.subst
```

---

## Attributes

---

## More on Implicit Arguments

---

## Notation

---

## Coercions

---

## Displaying Information

---

## Setting Options

---

## Elaboration Hints

---

## Using the Library

---


---

# 7. Inductive Types

---

## Enumerated Types

---

## Constructors with Arguments

---

## Inductively Defined Propositions

---

## Defining the Natural Numbers

---

## Other Recursive Data Types

---

## Tactics for Inductive Types

---

## Inductive Families

---

## Axiomatic Details

---

## Mutual and Nested Inductive Types

---

## Exercises

(private solutions in `src` directory)

---


---

# 8. Induction and Recursion

---

## Pattern Matching

---

## Wildcards and Overlapping Patterns

---

## Structural Recursion and Induction

---

## Well-Founded Recursion and Induction

---

## Mutual Recursion

---

## Dependent Pattern Matching

---

## Inaccessible Terms

---

## Match Expressions

---

## Exercises

(private solutions in `src` directory)

---

---

# 9. Structures and Records

---

## Declaring Structures

---

## Objects

---

## Inheritance

---

# 10. Type Classes

---

## Type Classes and Instances

---

## Chaining Instances

---

## Decidable Propositions

---

## Overloading with Type Classes

---

## Managing Type Class Inference

---

## Coercions using Type Classes

---


---

# 11. Axioms and Computation

---

## Historical and Philosophical Context

---

## Propositional Extensionality

---

## Function Extensionality

---

## Quotients

---

## Choice

---

## The Law of Excluded Middle

---

## Related or equivalent syntax

| Page(s) | Primary_Primitive_Syntax | First_Alternative_Syntax | Second_Alt_Syntax | description/context/example |
| --- | ---     | ---     | ---   | ---                         |
| 8   | `assume h:p` | `λ h:p`| `fun h:p` | hypotheses in a proof |
| 11  | `#reduce`      | `#eval`  |             | `#reduce` is trustworthy; `#eval` is fast |
| 11  | `def f (x:ℕ):ℕ := x+x` | `def f:ℕ → ℕ := λ(x:ℕ), x+x` |  |  |
| 13  | `let a := t1 in t2`    | `(λ a, t2) t1` |   | Warning: these are not the same! (see p. 13)  |
| 16  | `namespace` | `section` |    | `namespace` organizes data, lives on outer level; `section` declares variables for insertion in theorems |
| 18  | `sigma.fst(sigma.mk a b)` | `(sigma.mk a b).fst` | `(sigma.mk a b).1` | `variable a:α`; `variable b:βa`|
| 18  | `sigma.snd(sigma.mk a b)` | `(sigma.mk a b).snd` | `(sigma.mk a b).2` | `variable a:α`; `variable b:βa`|
| 24  | `Sort (u+1)`   | `Type u` |             |                       |
| 25, 26 | `definition`   | `theorem`| `lemma`     | but the elaborator treats these differently|
| 26  | `constant`     | `axiom`  |             |                       |
| 28 | `and.elim_left h` | `and.left h` | `h.left` | proves `p` when `h: p ∧ q` |
| 28 | `and.elim_right h`| `and.right h`| `h.right`| proves `q` when `h: p ∧ q` |
| 28 | `and.intro hp hq` | `⟨hp, hq⟩` |     | proves `p ∧ q` when `hp:p` and `hq:q` |
| 29 | `foo.bar e` | `e.bar` |  | `e` has type `foo` and `bar` is a function taking args of type `foo`|
| 30 | `or.intro_left _ hp` | `or.inl hp`     |   | proves `p ∨ q` when `hp:p`    |
| 30 | `or.intro_right _ hq`| `or.inr hq`     |   | proves `p ∨ q` when `hq:q`    |
| 30 | `false.elim ¬p ∧ p`  | `absurd p ∧ ¬p` |   | proves `false` from `¬p ∧ p`  |
| 31 | `true.intro`         | `trivial`       |   | proves `true` from nothing    |
| 31 | `iff.elim_left h`    | `iff.mp h` | `h.mp` | proves `p → q` from `h: p ↔ q`|
| 31 | `iff.elim_right h`   | `iff.mpr h`| `h.mpr`| proves `p ← q` from `h: p ↔ q`|
| 31 | `(λ (h:p), t) s`     | `have h:p, from s, t`  |   |   |
| 26, 37  | `∀ (x : α), p`  | `Π (x : α), p` |   | use ∀ for Props; use π for higher Types |
| 40 | `eq.refl _`   | `rfl`   |   | proof by reflexivity of equality  |
| 40 | `eq.subst h1 h2` | `h1 ▶ h2`  |   | proof by substitution  |
| 41 | `mul_add a b c` | `left_distrib a b c` |  | proves `a * (b + c) = a * b + a * c`|
| 41 | `add_mul a b c` | `right_distrib a b c` |  | proves `(a + b) * c = a * c + b * c`|
| 42 | `rewrite`   |`rw`        |  |  `a = b : by rw h` |
| 44 |  `Exists` | `exists` | `∃`  | `∃ (x : α), p x` = `exists (x : α), p x` = `Exists (λ x : α, p x)`|
| 44 |  `exists.intro t h` | `⟨t, h⟩` | | anonymous constructor notation for exists intro rule|
| 45 | `⟨w, ⟨hw.right, hw.left⟩⟩` | `⟨w, hw.right, hw.left⟩` | | |

--------------------------------------------------
