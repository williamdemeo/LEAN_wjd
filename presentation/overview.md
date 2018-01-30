### Lean Overview 

#### What is Lean?

+ a new, open source, interactive theorem prover 

+ principle developer: **Leonardo de Moura**, Microsoft Research

<center>http://leanprover.github.io</center>


---

### Perspective

Some systems currently in use with substantial mathematical
libraries:
+ **Mizar** (set theory)
+ **ACL2** (primitive recursive arithmetic)
+ **HOL4** (simple type theory)
+ **Isabelle** (simple type theory)
+ **HOL light** (simple type theory)
+ **PVS** classical dependent type theory)
+ **Coq** (constructive dependent type theory)
+ **Adga** (constructive dependent type theory)

Why develop another?

---

### Motivation

Why does the world need another proof assistant or functional programming language?

**Lean provides** 

1. a fresh start   

2. a system that incorporates best ideas from existing systems, and some
   novel solutions to common design problems
   
3. a hybrid interactive-automated system, being both
  - an interactive theorem prover with powerful automation
  - an automated reasoning tool capable of producing detailed proofs
    
4. a verified mathematical library
 
5. a programming environment in which one can
  - compute with objects using a precise formal semantics
  - reason about the results of computation
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

### Notable Features

+ written in C++, with **multi-core support**
+ **small trusted** kernel with independent type checkers
+ based on **constructive** dependent type theory but also supports **classical** axioms and deduction rules
+ supports **type class inference**
+ compiles structural/nested/mutual/well-founded recursive definitions down to **primitives**
+ **bytecode interpreter** for evaluating computable
definitions
+ supports **metaprogramming** via monadic interface to Lean internals
+ **profiler**, **debugger**, **simplifier** with conditional rewriting, arithmetic simplification
+ enthusiastic, talented **people** involved

---

### People of Lean
<span style="color:#e49436">**Code base:**</span> Leonardo de Moura, Gabriel Ebner, Sebastian Ullrich, Jared Roesch, Daniel Selsam

<span style="color:#e49436">**Libraries:**</span> Jeremy Avigad, Floris van Doorn, Leonardo de Moura, Robert Lewis, Gabriel Ebner, Johannes Hölzl, Mario Carneiro

<span style="color:#e49436">**Contributors:**</span>  Soonho Kong, Jakob von Raumer, Assia Mahboubi, Cody Roux, Parikshit Khanna, Ulrik Buchholtz, Favonia (Kuen-Bang Hou), Haitao Zhang, Jacob Gross, Andrew Zipperer, Joe Hurd
