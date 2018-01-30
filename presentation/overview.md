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

---

### Why develop another proof assistant?

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

### Goals

**Lean** may be used to 

+ verify mathematics  

+ verify hardware, software, and hybrid systems  

+ support reasoning and exploration  

+ support formal methods in education  

+ create an eminently powerful, usable system  

+ bring formal methods to the masses

---

### History of Lean

+ **2013** Project Started
 
+ **2015** Lean 2 announced
 
+ **2017** Lean 3 now available  
 
+ **2018** standard library and automation still under development  
 
(HoTT development is ongoing *in Lean 2 only*)

---

### Notable Features

+ written in C++, with **multi-core support**  
 
+ **small trusted** kernel with independent type checkers  

+ based on **constructive type theory** but supports **classical logic**  

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