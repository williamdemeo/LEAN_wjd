## Introduction to the Lean Prover

#### William DeMeo
[&lt;williamdemeo@gmail.com&gt;](mailto:williamdemeo@gmail.com)

#### CU Boulder Logic Seminar, 23 Jan 2018

---

### Main References

+ [Introduction to Lean](https://leanprover.github.io/introduction_to_lean/)  
leanprover.github.io/introduction_to_lean

+ [Theorem Proving in Lean](https://leanprover.github.io/theorem_proving_in_lean/)  
leanprover.github.io/theorem_proving_in_lean

---

## Lean Overview 

### What is Lean?

+ a new, open source, interactive theorem prover 

+ developed principally by **Leonardo de Moura** at Microsoft Research

<center>http://leanprover.github.io</center>


---

### Perspective

Some systems currently in use with substantial mathematical
libraries:
+ Mizar (set theory)
+ ACL2 (primitive recursive arithmetic)
+ HOL4 (simple type theory)
+ Isabelle (simple type theory)
+ HOL light (simple type theory)
+ PVS (classical dependent type theory)
+ Coq (constructive dependent type theory)
+ Adga (constructive dependent type theory)

Why develop another?

---

### Motivation

#### Why develop another?

+ It provides a fresh start.
+ Incorporates the best ideas/practices from existing provers, while avoiding shortcomings.
+ Incorporates some novel solutions to design problems.


---

### Motivation

Lean is an attempt to bring interactive and automated reasoning together with

+ an interactive theorem prover with powerful automation
+ an automated reasoning tool that
  - produces (detailed) proofs,
  - has a rich language,
  - can be used interactively,
  - is built on a verified mathematical library
+ a programming environment in which one can
  - compute with objects using a precise formal semantics,
  - reason about the results of computation,
  - create proof-producing automations

---

### Goals of Lean

+ verify mathematics  

+ verify hardware, software, and hybrid systems  

+ support reasoning and exploration  

+ support formal methods in education  

+ create an eminently powerful, usable system  

+ bring formal methods to the masses

---

### History of Lean

+ project began in 2013  
 
+ Lean 2 "announced" in summer 2015  
 
+ major rewrite, Lean 3, is now available  
 
+ standard library and automation under development  
 
+ HoTT development is ongoing in Lean 2

---

### People of Lean

**Code base:** Leonardo de Moura, Gabriel Ebner, Sebastian Ullrich, Jared Roesch, Daniel Selsam

**Libraries:** Jeremy Avigad, Floris van Doorn, Leonardo de Moura, Robert Lewis, Gabriel Ebner, Johannes Hölzl, Mario Carneiro

**Contributors:** Soonho Kong, Jakob von Raumer, Assia Mahboubi, Cody Roux, Parikshit Khanna, Ulrik Buchholtz, Favonia (Kuen-Bang Hou), Haitao Zhang, Jacob Gross, Andrew Zipperer, Joe Hurd

---

### Notable Features of Lean

+ based on a powerful dependent type theory
+ written in C++, with multi-core support
+ small trusted kernel with independent type checkers
+ supports constructive reasoning, quotients and extensionality, and classical reasoning
+ elegant syntax and a powerful elaborator
+ well-integrated type class inference
+ a function definition system compiles structural / nested / mutual / well-founded recursive definitions down to primitives
+ flexible means of writing declarative proofs and tactic-style proofs
+ server support for editors, with proof-checking and live information

---

### Notable Features (cont)

+ editor modes for Emacs and VSCode
+ a javascript version runs in a browser
+ a fast bytecode interpreter for evaluating computable
definitions
+ a powerful framework for metaprogramming via a monadic
interface to Lean internals
+ profiler and roll-your-own debugger
+ simplifier with conditional rewriting, arithmetic simplification
+ SMT-state extends tactics state with congruence closure,
e-matching
+ online documentation and courseware
+ enthusiastic, talented people involved

---

### Logical Foundations of Lean

Based on the *Calculus of Inductive Constructions*, with:

+ a hierarchy of (non-cumulative) universes, with a type Prop of
propositions at the bottom
+ dependent function types (Pi types)
+ inductive types (à la Dybjer)
Semi-constructive axioms and constructions:
+ quotient types (the existence of which imply function
extensionality)
+ propositional extensionality
A single classical axiom:
+ choice

---

### Logical Foundations

#### Calculus of Inductive Constructions

+ every expression has a **type** indicating what sort of object the expression denotes (eg a mathematical object like a natural number, a data type, an
assertion, a proof, etc). 
+ Lean implements the logical foundation called **dependent type theory** 
+ Specifically, the **Calculus of Inductive Constructions** a formal language with a small and precise set of rules that governs the formation of expressions. 


---

### Logical Foundations

#### Type Universes

+ Lean has a hierarchy of non-cumulative type universes:
  ```
  Sort 0, Sort 1, Sort 2, Sort 3, . . .
  ```

+ These can also be written:
  ```
  Prop, Type 0, Type 1, Type 2, . . .
  ```

+ `Prop` is *impredicative* and definitionally *proof irrelevant*.   
  That is, if 
  ```
  p : Prop, s : p, t : p
  ```
  then `s` and `t` are definitionally equal.

---

### Logical Foundations

Lean has
+ **dependent function types**  
  Π x : α, β x, with the usual reduction rule (λ x, t) s = t [s / x]

+ **eta equivalence for functions**  
  t and λ x, t x are definitionally equal

+ **let definitions**  
  let x := s in t, with the expected reduction rule

---

### Logical Foundations

Lean implements **inductive families** with **primitive recursors**, with the
expected computation rules.

```
inductive vector (α : Type u) : N → Type u
| nil : vector 0
| cons {n : N} (a : α) (v : vector n) : vector (n+1)
#check (vector : Type u → N → Type u)
#check (vector.nil : Π α : Type u, vector α 0)
#check (@vector.cons : Π {α : Type u} {n : N},
  α → vector α n → vector α (n + 1))
#check (@vector.rec :
  Π {α : Type u} {C : Π (n : N), vector α n → Sort u},
    C 0 (vector.nil α) →
    (Π {n : N} (a : α) (v : vector α n), C n v →
                          C (n + 1) (vector.cons a v)) →
    Π {n : N} (v : vector α n), C n v)
```
