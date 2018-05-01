# Theorem Proving In Lean: Notes Part 2

This markdown file is a collection of annotated excerpts from Chapters 7--11 of the online book
[Theorem Proving in Lean](https://leanprover.github.io/theorem_proving_in_lean/theorem_proving_in_lean.pdf).

I made this file for myself while learning Lean, for my own future reference. This is not original work and is not meant for public consumption.

---

<!-- TOC depthFrom:1 depthTo:6 withLinks:1 updateOnSave:1 orderedList:0 -->

- [Theorem Proving In Lean: Notes Part 2](#theorem-proving-in-lean-notes-part-2)
- [0. Syntactic Alternatives](#0-syntactic-alternatives)
- [7. Inductive Types](#7-inductive-types)
	- [Enumerated Types](#enumerated-types)
	- [Constructors with Arguments](#constructors-with-arguments)
	- [Inductively Defined Propositions](#inductively-defined-propositions)
	- [Defining the Natural Numbers](#defining-the-natural-numbers)
	- [Other Recursive Data Types](#other-recursive-data-types)
	- [Tactics for Inductive Types](#tactics-for-inductive-types)
	- [Inductive Families](#inductive-families)
	- [Axiomatic Details](#axiomatic-details)
	- [Mutual and Nested Inductive Types](#mutual-and-nested-inductive-types)
	- [Exercises](#exercises)
- [8. Induction and Recursion](#8-induction-and-recursion)
	- [Pattern Matching](#pattern-matching)
	- [Wildcards and Overlapping Patterns](#wildcards-and-overlapping-patterns)
	- [Structural Recursion and Induction](#structural-recursion-and-induction)
	- [Well-Founded Recursion and Induction](#well-founded-recursion-and-induction)
	- [Mutual Recursion](#mutual-recursion)
	- [Dependent Pattern Matching](#dependent-pattern-matching)
	- [Inaccessible Terms](#inaccessible-terms)
	- [Match Expressions](#match-expressions)
	- [Exercises](#exercises)
- [9. Structures and Records](#9-structures-and-records)
	- [Declaring Structures](#declaring-structures)
	- [Objects](#objects)
	- [Inheritance](#inheritance)
- [10. Type Classes](#10-type-classes)
	- [Type Classes and Instances](#type-classes-and-instances)
	- [Chaining Instances](#chaining-instances)
	- [Decidable Propositions](#decidable-propositions)
	- [Overloading with Type Classes](#overloading-with-type-classes)
	- [Managing Type Class Inference](#managing-type-class-inference)
	- [Coercions using Type Classes](#coercions-using-type-classes)
- [11. Axioms and Computation](#11-axioms-and-computation)
	- [Historical and Philosophical Context](#historical-and-philosophical-context)
	- [Propositional Extensionality](#propositional-extensionality)
	- [Function Extensionality](#function-extensionality)
	- [Quotients](#quotients)
	- [Choice](#choice)
	- [The Law of Excluded Middle](#the-law-of-excluded-middle)
- [Appendix](#appendix)
	- [A.1. Emacs lean-mode](#a1-emacs-lean-mode)
		- [lean-mode key bindings and commands](#lean-mode-key-bindings-and-commands)
	- [A.2. Syntactic Alternatives](#a2-syntactic-alternatives)

<!-- /TOC -->
---

## 0. Syntactic Alternatives

In Lean it is often possible to do something in more than one way, and while this can be helpful and convenient, it may cause confusion if we're unfamiliar with the different syntax that may be used to represent a single semantic entity.  The following is a table of syntactic alternatives, and pages on which they are introduced in the Theorem Proving tutorial.

| Sec. | Page(s) | Primary_Primitive_Syntax | First_Alternative_Syntax | Second_Alt_Syntax | description/context/example |
|--- | --- | ---     | ---     | ---   | ---                         |
| 2.3 | 11  | `#reduce`      | `#eval`  |             | `#reduce` is trustworthy; `#eval` is fast |
| 2.4 | 11  | `def f (x:ℕ):ℕ := x+x` | `def f:ℕ → ℕ := λ(x:ℕ), x+x` |  |  |
| 2.5 | 13  | `let a := t1 in t2`    | `(λ a, t2) t1` |   | Warning: these are not the same! (see p. 13)  |
| 2.7 | 16  | `namespace` | `section` |    | `namespace` organizes data, lives on outer level; `section` declares variables for insertion in theorems |
| 2.8 | 18  | `sigma.fst(sigma.mk a b)` | `(sigma.mk a b).fst` | `(sigma.mk a b).1` | `variable a:α`; `variable b:βa`|
| 2.8 | 18  | `sigma.snd(sigma.mk a b)` | `(sigma.mk a b).snd` | `(sigma.mk a b).2` | `variable a:α`; `variable b:βa`|
| 3.1 | 24  | `Sort (u+1)`   | `Type u` |             |                       |
| 3.2 | 25, 26 | `definition`   | `theorem`| `lemma`     | but the elaborator treats these differently|
| 3.2 | 26  | `constant`     | `axiom`  |             |                       |
| 3.3 | 28 | `and.elim_left h` | `and.left h` | `h.left` | proves `p` when `h: p ∧ q` |
| 3.3 | 28 | `and.elim_right h`| `and.right h`| `h.right`| proves `q` when `h: p ∧ q` |
| 3.3 | 28 | `and.intro hp hq` | `⟨hp, hq⟩` |     | proves `p ∧ q` when `hp:p` and `hq:q` |
| 3.3 | 29 | `foo.bar e` | `e.bar` |  | `e` has type `foo` and `bar` is a function taking args of type `foo`|
| 3.3 | 30 | `or.intro_left _ hp` | `or.inl hp`     |   | proves `p ∨ q` when `hp:p`    |
| 3.3 | 30 | `or.intro_right _ hq`| `or.inr hq`     |   | proves `p ∨ q` when `hq:q`    |
| 3.3 | 30 | `false.elim ¬p ∧ p`  | `absurd p ∧ ¬p` |   | proves `false` from `¬p ∧ p`  |
| 3.3 | 31 | `true.intro`         | `trivial`       |   | proves `true` from nothing    |
| 3.3 | 31 | `iff.elim_left h`    | `iff.mp h` | `h.mp` | proves `p → q` from `h: p ↔ q`|
| 3.3 | 31 | `iff.elim_right h`   | `iff.mpr h`| `h.mpr`| proves `p ← q` from `h: p ↔ q`|
| 3.3 | 31 | `(λ (h:p), t) s`     | `have h:p, from s, t`  |   |   |
| 4.1 | 26, 37  | `∀ (x : α), p`  | `Π (x : α), p` |   | use ∀ for Props; use π for higher Types |
|4.2 | 40 | `eq.refl _`   | `rfl`   |   | proof by reflexivity of equality  |
| 4.2 | 40 | `eq.subst h1 h2` | `h1 ▶ h2`  |   | proof by substitution  |
| 4.2 | 41 | `mul_add a b c` | `left_distrib a b c` |  | proves `a * (b + c) = a * b + a * c`|
| 4.2| 41 | `add_mul a b c` | `right_distrib a b c` |  | proves `(a + b) * c = a * c + b * c`|
| 4.3 | 42 | `rewrite`   |`rw`        |  |  `a = b : by rw h` |
| 4.4 | 44 |  `Exists` | `exists` | `∃`  | `∃ (x : α), p x` = `exists (x : α), p x` = `Exists (λ x : α, p x)`|
| 4.4 | 44 |  `exists.intro t h` | `⟨t, h⟩` | | anonymous constructor notation for exists intro rule|
| 4.4 | 45 | `⟨w, ⟨hw.right, hw.left⟩⟩` | `⟨w, hw.right, hw.left⟩` | | |
| 5.3 | 60 | `right` (resp `left`)  (tactic) | `apply or.inl` (resp `apply or.inr`)| | |

--------------------------------------------------

## 7. Inductive Types

---
### 7.1. Enumerated Types

---
### 7.2. Constructors with Arguments

---
### 7.3. Inductively Defined Propositions

---
### 7.4. Defining the Natural Numbers

---
### 7.5. Other Recursive Data Types

---
### 7.6. Tactics for Inductive Types

---
### 7.7. Inductive Families

---
### 7.8. Axiomatic Details

---
### 7.9. Mutual and Nested Inductive Types

---
### 7.10. Exercises

(private solutions in `src` directory)

---

## 8. Induction and Recursion

---
### 8. Induction and Recursion

---
### 8.1. Pattern Matching

---
### 8.2. Wildcards and Overlapping Patterns

---
### 8.3. Structural Recursion and Induction

---
### 8.4. Well-Founded Recursion and Induction

---
### 8.5. Mutual Recursion

---
### 8.6. Dependent Pattern Matching

---
### 8.7. Inaccessible Terms

---
### 8.8. Match Expressions

---
### 8.9. Exercises

(private solutions in `src` directory)

---

## 9. Structures and Records

---
### 9.1. Declaring Structures

---
### 9.2. Objects

---
### 9.3. Inheritance

---
## 10. Type Classes

---
### 10.1. Type Classes and Instances

---
### 10.2. Chaining Instances

---
### 10.3. Decidable Propositions

---
### 10.4. Overloading with Type Classes

---
### 10.5. Managing Type Class Inference

---
### 10.6. Coercions using Type Classes

---
## 11. Axioms and Computation

---
### 11.1. Historical and Philosophical Context

---
### 11.2. Propositional Extensionality

---
### 11.3. Function Extensionality

---
### 11.4. Quotients

---
### 11.5. Choice

---
### 11.6. The Law of the Excluded Middle

---

## Appendix

### A.1. Emacs lean-mode

For more details about `lean-mode`, refer to the official [lean-mode repository](https://github.com/leanprover/lean-mode).
The remainder of this section are excerpts from the README.md file of 
[lean-mode repository](https://github.com/leanprover/lean-mode).

If things are working correctly, you should see the word ``Lean`` in the
Emacs mode line when you open a file with extension `.lean`.

#### lean-mode key bindings and commands

| Key                | Function                                                                        |
|--------------------|---------------------------------------------------------------------------------|
| <kbd>M-.</kbd>     | jump to definition in source file (`lean-find-definition`)                      |
| <kbd>C-c C-k</kbd> | shows the keystroke needed to input the symbol under the cursor                 |
| <kbd>C-c C-x</kbd> | execute lean in stand-alone mode (`lean-std-exe`)                               |
| <kbd>C-c SPC</kbd> | run a command on the hole at point (`lean-hole`)                                |
| <kbd>C-c C-d</kbd> | show a searchable list of definitions (`helm-lean-definitions`)                 |
| <kbd>C-c C-g</kbd> | toggle showing current tactic proof goal (`lean-toggle-show-goal`)              |
| <kbd>C-c C-n</kbd> | toggle showing next error in dedicated buffer (`lean-toggle-next-error`)        |
| <kbd>C-c C-b</kbd> | toggle showing output in inline boxes (`lean-message-boxes-toggle`)             |
| <kbd>C-c C-r</kbd> | restart the lean server (`lean-server-restart`)                                 |
| <kbd>C-c ! n</kbd> | flycheck: go to next error                                                      |
| <kbd>C-c ! p</kbd> | flycheck: go to previous error                                                  |
| <kbd>C-c ! l</kbd> | flycheck: show list of errors                                                   |

In the default configuration, the Flycheck annotation `FlyC:n/n` indicates the
number of errors / responses from Lean; clicking on `FlyC` opens the Flycheck menu.


---

### A.2. Syntactic Alternatives

In Lean it is often possible to do something in more than one way, and while this can be helpful and convenient, it may cause confusion if we're unfamiliar with the different syntax that may be used to represent a single semantic entity.  The following is a table of syntactic alternatives, and pages on which they are introduced in the Theorem Proving tutorial.

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
