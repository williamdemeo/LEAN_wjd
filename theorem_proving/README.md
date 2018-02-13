## theorem_proving

This directory collects notes that I took while working through the online book 
[Theorem Proving in Lean](https://leanprover.github.io/theorem_proving_in_lean/theorem_proving_in_lean.pdf).

### Useful commands

 `C-c C-b`, `C-c C-x`, `C-c C-r`

To execute the commands in the file `overview.lean`, load the file into emacs and then run

+ `C-c C-b` to see the results inline, or 

+ `C-c C-x` to execute the whole file

+ when hovering over a `#check` statement, the type of the expression appears in a pop-up or in the comman buffer.

+ If the `hover-over` feature is not working , then try `C-c C-r` to re-read (re-typecheck) the file.

---
	
## Theorem Proving In Lean

The remainder of this file is a collection of notes and excerpts from the tutorial [Theorem Proving in Lean](https://leanprover.github.io/documentation/).

---

**Contents of Sequel**

- [Function Abstraction and Evaluation](#function-abstraction-and-evaluation)
- [Introducing Definitions](#introducing-definitions)
- [Local Definitions](#local-definitions)
- [Variables and Sections](#variables-and-sections)
- [Namespaces](#namespaces)
- [Dependent Types](#dependent-types)
  - [Sigma Types (aka dependent products)](#sigma-types-aka-dependent-products)
  - [Implicit Arguments](#implicit-arguments)
- [Exercises](#exercises)

---

## 2. Dependent Type Theory
Dependent type theory is a powerful and expressive language, allowing us to
express complex mathematical assertions, write complex hardware and software
specifications, and reason about both of these in a natural and uniform
way. Lean is based on a version of dependent type theory known as the *Calculus
of Constructions*, with a countable hierarchy of non-cumulative universes and
inductive types. Much of what this means is described below. 

---

### Simple Type Theory

As a foundation for mathematics, set theory has a simple ontology that is rather
appealing. Everything is a set, including numbers, functions, triangles,
stochastic processes, and Riemannian manifolds.

For many purposes, including formal theorem proving, it is better to have an
infrastructure that helps manage and keep track of the various kinds of
mathematical objects we work with. "Type theory" gets its name from the fact 
that every expression has an associated *type*. For example, in a given 
context, ``x + 0`` may denote a natural number and ``f`` may denote a function
on the natural numbers. 

---

Here are some examples of how we can declare objects in Lean and check their types.

```scala
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

    -- Try some examples of your own.
```

---

#### Comments, constants, and check

+ Any text between the ``/-`` and ``-/`` constitutes a comment that is ignored.

+ Similarly, two dashes indicate that the rest of the line contains a
  comment. Comment blocks can be nested. 

+ The ``constant`` and ``constants`` commands introduce new constant symbols into
  the working environment. 

+ The ``#check`` command asks Lean to report their types; commands that query
  the system for information typically begin with the hash symbol. 
  
+ Declaring new objects in this way is a good way to experiment with the system,
  but it is ultimately undesirable: Lean is a foundational system, and it
  provides us with powerful mechanisms to *define* all the mathematical objects
  we need, rather than simply postulating them. 
---

#### New Types from Old

+ What makes simple type theory powerful is that one can build new types out of
  others. For example, if ``α`` and ``β`` are types, ``α → β`` denotes the type
  of functions from ``α`` to ``β``, and ``α × β`` denotes the cartesian product,
  that is, the type of ordered pairs consisting of an element of ``α`` paired
  with an element of ``β``. 

```scala
    constants m n : nat
    constant f : nat → nat           -- type the arrow as "\to" or "\r"
    constant f' : nat -> nat         -- alternative ASCII notation
    constant f'' : ℕ → ℕ             -- alternative notation for nat
    constant p : nat × nat           -- type the product as "\times"
    constant q : prod nat nat        -- alternative notation
    constant g : nat → nat → nat
    constant g' : nat → (nat → nat)  -- has the same type as g!
    constant h : nat × nat → nat
    constant F : (nat → nat) → nat   -- a "functional"

    #check f               -- ℕ → ℕ
    #check f n             -- ℕ
    #check g m n           -- ℕ
    #check g m             -- ℕ → ℕ
    #check (m, n)          -- ℕ × ℕ
    #check p.1             -- ℕ
    #check p.2             -- ℕ
    #check (m, n).1        -- ℕ
    #check (p.1, n)        -- ℕ × ℕ
    #check F f             -- ℕ
```

---

#### Some Basic Syntax

+ The unicode arrow ``→`` is obtained by typing ``\to`` or ``\r``, 
  but the ASCII alternative ``->`` also works; ``nat -> nat`` and 
  ``nat → nat`` mean the same thing---the type of functions from nat to nat.
+ The symbol ``ℕ`` is unicode notation for ``nat`` and is obtained by ``\nat``. 
+ The symbol ``×`` for is obtained from ``\times``. 
+ Lower-case greek letters, like ``α``, ``β``, and ``γ``, are typically used to 
  range over types; enter them with, e.g., ``\a``, ``\b``, and ``\g``.

---

+ When writing type expressions, arrows associate to the *right*; for example, the
  type of ``g`` is ``nat → (nat → nat)``. Thus ``g`` is a function that takes
  natural numbers and returns another function that takes a natural number and returns a
  natural number.  This  allows us to "partially apply" the function ``g``. 
  
+ In Lean, ``(m, n)`` denotes the ordered pair of ``m`` and ``n``, and if ``p``
  is a pair, ``p.1`` and ``p.2`` denote the two projections.

---

### Types as Objects

One way in which Lean's dependent type theory extends simple type theory is that
types themselves --- entities like ``nat`` and ``bool`` --- are first-class
citizens, which is to say that they themselves are objects of study. For that to
be the case, each of them also has to have a type. 

```scala
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
We see that each one of the expressions above is an object of type ``Type``. 

---

We can also declare new constants and constructors for types: 

```scala
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

Indeed, we have already seen an example of a function of type 
``Type → Type → Type``, namely, the Cartesian product. 

```scala
    constants α β : Type

    #check prod α β       -- Type
    #check prod nat nat   -- Type
```

Here is another example: given any type ``α``, the type ``list α`` denotes the
type of lists of elements of type ``α``. 

```scala
    constant α : Type

    #check list α    -- Type
    #check list nat  -- Type
```

---
#### The Type of Type?

Given that every expression in Lean has a type, it is natural to ask what type does ``Type`` itself have.

```scala
    #check Type      -- Type 1
```
This reveals the first level of Lean's infinite hierarchy of types.

```scala
    #check Type     -- Type 1
    #check Type 1   -- Type 2
    #check Type 2   -- Type 3
    #check Type 3   -- Type 4
    #check Type 4   -- Type 5
```

---

#### The Hierarchy of Type Universes

+ ``Type 0`` is a universe of "small" or "ordinary" types; 
+ ``Type 1`` is a larger universe of types, which contains ``Type 0`` as an element; 
+ ``Type 2`` is a larger still universe of types, which contains ``Type 1`` as an element;
 
and so on... there is a ``Type n`` for every natural number``n``.

``Type`` is an abbreviation for ``Type 0``: 

```scala
    #check Type
    #check Type 0
```

---

#### The Prop type

There is a very special type at the bottom of the hierarchy called ``Prop``.
It has type `Type 0`. We will discuss ``Prop`` at length below.

---

We want some operations to be *polymorphic* over type universes. For example, 
``list α`` should make sense for any type ``α``, no matter which type universe
``α`` lives in. This explains the type annotation of the function ``list``.

```scala
    #check list    -- Type u_1 → Type u_1
```
Here ``u_1`` is a variable ranging over type levels. The output of the ``#check`` 
command means whenever ``α`` has type ``Type n``, ``list α`` also has type ``Type n``. 
The function ``prod`` is similarly polymorphic.

```scala
    #check prod    -- Type u_1 → Type u_2 → Type (max u_1 u_2)
```

---

#### Polymorphic constants and variables

To define polymorphic constants and variables, Lean allows us to declare universe variables explicitly.

```scala
    universe u
    constant α : Type u
    #check α
```
This is useful for giving type constructions *as much generality as possible*. 

*The ability to treat type constructors as instances of ordinary mathematical
functions is a powerful feature of dependent type theory.*

---

### Function Abstraction and Evaluation

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

### Introducing Definitions

There are a number of ways to define functions in Lean.  You can use 
1. λ-abstraction,
   ```scala
   def double: ℕ → ℕ := λ x, x + x
   ```
2. λ-abstraction with some type inference,
   ```scala
   def double := λ (x : ℕ), x + x
   ```
3. or the syntax (that looks familiar to users of Scala),
   ```scala
   def double (x: ℕ) : ℕ := x + x
   ```
  
In the last version above, we specified the input argument and its 
type `(x: ℕ)` as well as the output type (ℕ).  The three functions 
defined above are definitionally equal.

The types of the arguments of a function can also be passed as arguments.
```scala
def compose (α β γ : Type) (g: β → γ) (f: α → β) (x: α) : γ := g (f x)
```

---

### Local Definitions

The expression `let a := 2 in t` is *definitionally equal* to the result of 
replacing every occurrence of `a` in `t` by `2`.  For example,

```scala
def t (x : ℕ) : ℕ := 
  let y := x + x in y * y
	
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
	
```scala
def foo := let a := nat  in λ x : a, x + 2
/-
def bar := (λ a, λ x : a, x + 2) nat
-/
```

---

### Variables and Sections

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

```scala
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ := g (f x)
def do_twice (α : Type) (h : α → α) (x : α) : α := h (h x)
def do_thrice (α : Type) (h : α → α) (x : α) : α := h (h (h x))
```

This can be tedious, however, so Lean provides the ``variable`` and ``variables`` 
commands to make such declarations look global.

```scala
variables (α β γ : Type)
def compose (g : β → γ) (f : α → β) (x : α) : γ := g (f x)
def do_twice (h : α → α) (x : α) : α := h (h x)
def do_thrice (h : α → α) (x : α) : α := h (h (h x))
```

---

We can declare variables of any type, not just ``Type`` itself.

```scala
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

---

Thus, a variable stays in scope until the eof, and we can't declare another
variable with the same name. Sometimes, however, it is useful to limit the scope
of a variable. For that purpose, Lean provides the notion of a ``section``.

```scala
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


### Namespaces

Lean provides the ability to group definitions into nested, hierarchical *namespaces*.

```scala
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

``open`` brings the shorter names into the current context. Often, when we
import a theory file, we want to open some of the namespaces it contains, to
have access to short identifiers. But sometimes we want to leave this info
hidden, for example, when they conflict with identifiers in another namespace we
want to use. Thus namespaces give us a way to manage our working environment. 

For example, Lean groups definitions and theorems involving lists into a namespace ``list``.

```scala
#check list.nil
#check list.cons
#check list.append
```

The command ``open list`` makes the shorter names available:

```scala
open list
#check nil
#check cons
#check append
```

Like sections, namespaces can be nested.

```scala
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

Namespaces that have been closed can later be reopened, even in another file.


```scala
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

Like sections, nested namespaces have to be closed in the order they are
opened. Also, a namespace cannot be opened within a section; namespaces have to
live on the outer levels. 

*Namespaces and sections serve different purposes.*

+ **Namespaces** *organize data*;
+ **Sections** *declare variables for insertion in theorems*. 

In many respects, however, a ``namespace ... end`` block behaves like a ``section ... end``
block. In particular, if you use the ``variable`` command within a namespace,
its scope is limited to the namespace. Similarly, if you use an ``open`` command
within a namespace, its effects disappear when the namespace is closed. 

---

### Dependent Types

An important goal in Lean is to *prove* things about the objects we define, and
the next chapter will introduce you to Lean's mechanisms for stating theorems
and constructing proofs. Meanwhile, let us remain on the topic of defining
objects in dependent type theory for just a moment longer. In this section, we
will explain what makes dependent type theory *dependent*, and why dependent
types are useful.

The short explanation is that what makes dependent type theory dependent is that
*types can depend on parameters*. You have already seen a nice example of this:
the type ``list α`` depends on the argument ``α``, and this dependence is what
distinguishes ``list ℕ`` and ``list bool``. For another example, consider the
type ``vec α n``, the type of vectors of elements of ``α`` of length ``n``. 
This type depends on *two* parameters: the type ``α : Type`` of the elements in
the vector and the length ``n : ℕ``. 

Suppose we wish to write a function ``cons`` that inserts a new element at the
head of a list. What type should ``cons`` have? Such a function is
*polymorphic*: we expect the ``cons`` function for ``ℕ``, ``bool``, or an
arbitrary type ``α`` to behave the same way. So it makes sense to take the type
to be the first argument to ``cons``, so that for any type, ``α``, ``cons α`` is
the insertion function for lists of type ``α``. In other words, for every ``α``,
``cons α`` is the function that takes an element ``a : α`` and a list 
``l : list α``, and returns a new list, so we have ``cons α a l : list α``. 

It's clear that ``cons α`` has type ``α → list α → list α``. But what type 
should ``cons`` have? A first guess might be 
```scala
Type → α → list α → list α``
```
but, on reflection, this does not make sense: the ``α`` in this expression
does not refer to anything, whereas it should refer to the argument of type
``Type``. In other words, *assuming* ``α : Type`` is the first argument to the
function, the type of the next two elements are ``α`` and ``list α``. These
types vary depending on the first argument, ``α``. 

This is an instance of a **Pi type**, or **dependent function type**. 
If ``α : Type`` and ``β : α → Type``, then ``β`` is a family of types over ``α``, 
that is, a type ``β a`` for each ``a : α``. In that case, the type ``Π x : α, β x``
denotes the type of functions ``f`` such that, if ``a : α``, then ``f a`` is an element
of ``β a``. In other words, the type of the value returned by ``f`` depends on its input. 

Notice that ``Π x : α, β`` makes sense for any expression ``β : Type``. 
If the value of ``β`` depends on ``x`` (as above), then ``Π x : α, β`` 
denotes a dependent function type. If ``β`` does not depend on ``x``, then 
``Π x : α, β`` is no different from the type ``α → β``. Indeed, in dependent
type theory (and in Lean), the Pi construction is fundamental, and ``α → β`` is 
just notation for ``Π x : α, β`` when ``β`` does not depend on ``α``.

Returning to the example of lists, we can model some basic list operations as
follows. We use ``namespace hide`` to avoid a naming conflict with the ``list``
type defined in the standard library. 

```scala
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

You can enter the symbol ``Π`` by typing ``\Pi``. Here, ``nil`` is intended to
denote the empty list, ``head`` and ``tail`` return the first element of a list
and the remainder, respectively. The constant ``append`` is intended to denote
the function that concatenates two lists. 

We emphasize that these constant declarations are only for the purposes of
illustration. The ``list`` type and all these operations are, in fact, *defined*
in Lean's standard library, and are proved to have the expected
properties. Moreover, as the next example shows, the types indicated above are
essentially the types of the objects that are defined in the library. (We will
explain the ``@`` symbol and the difference between the round and curly brackets
momentarily.) 

```scala
open list
#check list     -- Type u_1 → Type u_1
#check @cons    -- Π {α : Type u_1}, α → list α → list α
#check @nil     -- Π {α : Type u_1}, list α
#check @head    -- Π {α : Type u_1} [_inst_1 : inhabited α], list α → α
#check @tail    -- Π {α : Type u_1}, list α → list α
#check @append  -- Π {α : Type u_1}, list α → list α → list α
```
There is a subtlety in the definition of ``head``: the type ``α`` is required to
have at least one element, and when passed the empty list, the function must
determine a default element of the relevant type. We will explain how this is
done later. 

Vector operations are handled similarly:

```scala
universe u
constant vec : Type u → ℕ → Type u
namespace vec
  constant empty : Π α : Type u, vec α 0
  constant cons : Π (α : Type u) (n : ℕ), α → vec α n → vec α (n + 1)
  constant append : Π (α : Type u) (n m : ℕ),  vec α m → vec α n → vec α (n + m)
end vec
```

#### Sigma Types (aka dependent products)

One more important example is the concept of *Sigma types*, denoted ``Σ x : α, β x``, which are known as *dependent products*. This is the type of pairs ``sigma.mk a b`` where ``a : α`` and ``b : β a``.

Just as Pi types ``Π x : α, β x`` generalize the notion of a function type ``α → β`` by allowing ``β`` to depend on ``α``, Sigma types ``Σ x : α, β x`` generalize the cartesian product ``α × β`` in the same way: in the expression ``sigma.mk a b``, the type of the second element of the pair, ``b : β a``, depends on the first element of the pair, ``a : α``.

```scala
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

``(sigma.mk a b).1`` and ``(sigma.mk a b).2`` are short for 
``sigma.fst (sigma.mk a b)`` and ``sigma.snd (sigma.mk a b)`` (resp.), and these reduce to ``a`` and ``b`` (resp.).

### Implicit Arguments

Suppose we have an implementation of lists as described above.

```scala
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

Then, given a type ``α``, some elements of ``α``, and some lists of elements of ``α``, we can construct new lists using the constructors.

```scala
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

Because the constructors are polymorphic over types, we have to insert the type ``α`` as an argument repeatedly. But this information is redundant: one can infer the argument ``α`` in ``cons α a (nil α)`` from the fact that the second argument, ``a``, has type ``α``. One can similarly infer the argument in ``nil α``, not from anything else in that expression, but from the fact that it is sent as an argument to the function ``cons``, which expects an element of type ``list α`` in that position.

This is a central feature of dependent type theory: terms carry a lot of information, and often some of that information can be inferred from the context. In Lean, one uses an underscore, ``_``, to specify that the system should fill in the information automatically. This is known as an "implicit argument."

```scala
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
It is still tedious, however, to type all these underscores. When a function takes an argument that can generally be inferred from context, Lean allows us to specify that this argument should, by default, be left implicit. This is done by putting the arguments in curly braces, as follows:

```scala
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

All that has changed are the braces around ``α : Type u`` in the declaration of the variables. We can also use this device in function definitions:

```scala

    universe u
    def ident {α : Type u} (x : α) := x

    variables α β : Type u
    variables (a : α) (b : β)

    #check ident      -- ?M_1 → ?M_1
    #check ident a    -- α
    #check ident b    -- β
```

This makes the first argument to ``ident`` implicit. Notationally, this hides the specification of the type, making it look as though ``ident`` simply takes an argument of any type. In fact, the function ``id`` is defined in the standard library in exactly this way. We have chosen a nontraditional name here only to avoid a clash of names.

Variables can also be specified as implicit when they are declared with
the ``variables`` command:

```scala
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
This definition of ``ident`` here has the same effect as the one above.

Lean has very complex mechanisms for instantiating implicit arguments, and we will see that they can be used to infer function types, predicates, and even proofs. The process of instantiating these "holes," or "placeholders," in a term is often known as *elaboration*. The presence of implicit arguments means that at times there may be insufficient information to fix the meaning of an expression precisely. An expression like ``id`` or ``list.nil`` is said to be *polymorphic*, because it can take on different meanings in different contexts.

One can always specify the type ``T`` of an expression ``e`` by writing ``(e : T)``. This instructs Lean's elaborator to use the value ``T`` as the type of ``e`` when trying to resolve implicit arguments. In the second pair of examples below, this mechanism is used to specify the desired types of the expressions ``id`` and ``list.nil``:

```scala
#check list.nil             -- list ?M1
#check id                   -- ?M1 → ?M1

#check (list.nil : list ℕ)  -- list ℕ
#check (id : ℕ → ℕ)         -- ℕ → ℕ
```

Numerals are overloaded in Lean, but when the type of a numeral cannot be inferred, Lean assumes, by default, that it is a natural number. So the expressions in the first two ``#check`` commands below are elaborated in the same way, whereas the third ``#check`` command interprets ``2`` as an integer.

```scala
#check 2            -- ℕ
#check (2 : ℕ)      -- ℕ
#check (2 : ℤ)      -- ℤ
--

Sometimes, however, we may find ourselves in a situation where we have declared an argument to a function to be implicit, but now want to provide the argument explicitly. If ``foo`` is such a function, the notation ``@foo`` denotes the same function with all the arguments made explicit.

```scala
variables α β : Type
variables (a : α) (b : β)

#check @id        -- Π {α : Type u_1}, α → α
#check @id α      -- α → α
#check @id β      -- β → β
#check @id α a    -- α
#check @id β b    -- β
  
```

Notice that now the first ``#check`` command gives the type of the identifier, ``id``, without inserting any placeholders. Moreover, the output indicates that the first argument is implicit.

### Exercises

1. Define the function ``Do_Twice``, as described in [Introducing Definitions](#introducing-definitions).

2. Define the functions ``curry`` and ``uncurry``, as described in [Introducing Definitions](#introducing-definitions).

3. Above, we used the example ``vec α n`` for vectors of elements of type ``α`` of length ``n``. Declare a constant ``vec_add`` that could represent a function that adds two vectors of natural numbers of the same length, and a constant ``vec_reverse`` that can represent a function that reverses its argument. Use implicit arguments for parameters that can be inferred. Declare some variables and check some expressions involving the constants that you have declared.

4. Similarly, declare a constant ``matrix`` so that ``matrix α m n`` could represent the type of ``m`` by ``n`` matrices. Declare some constants to represent functions on this type, such as matrix addition and multiplication, and (using ``vec``) multiplication of a matrix by a vector. Once again, declare some variables and check some expressions involving the constants that you have declared.




--------------------------------------------------

## 3. Propositions and Proofs

### Propositions as Types

---

### Working with Propositions as Types

---

### Propositional Logic

---

#### Conjunction

---

#### Disjunction

---

#### Negation and Falsity

---

#### Logical Equivalence

---

### Introducing Auxiliary Subgoals

---

### Classical Logic

---

### Examples of Propositional Validities

---

### Exercises

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

### The Law of the Excluded Middle


--------------------------------------------------
Sorry I wasn't prepared to demonstrate a simple inductive proof today.  As I mentioned, I'm *very* rusty.



In this post, I'll show a couple of ways to do simple proofs-by-induction over nat, but this requires that we know how to "unify" two terms that we believe are "obviously" the same.  We do that with "equality reflection," so I'll explain that first.  (Below TPL stands for the "Theorem Proving in Lean" tutorial.)



Lean defines, for all primitive types, the equality relation `eq` (we'll see *how* `eq` is defined later in Ch 7 of TPL). There are three built-in definitions associated with `eq` which correspond to the three properties that make `eq` an equivalence relation over the given type.  Specifically we have (Sec 4.2 of TPL) 









In Lean, reflexivity, `eq.refl` is actually more powerful than in other proof systems. This is because equality in Lean is extensional.  Recall that terms in Lean's logical framework has a computational interpretation that considers two terms that reduce to a common normal form are definitionally equal. As a result, some nontrivial identities can be proved very simply by reflexivity (relying on Lean to handle the reductions to the common normal form). Here are a few examples.







Each line beginning with the keyword `example` is a full-fledged formal proof (by reflexivity of extensional equality) of the given equality. The first case proves that $$(\lambda x, f x) a$$ is definitionally equal to $$f a$$



Since the expression `eq.refl _` is so common, Lean has a special abbreviation for it.  Spcifically, `rfl` is an alias for `eq.refl _`.



Now, we can prove the fact that Matt wrote on the board today, which we will need when proving `add_assoc.`  This happens to be another example where we need nothing more that `rfl` :



`theorem add_succ (m n : nat) :  m + succ n = succ (m + n) := rfl`
