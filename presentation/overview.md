### Lean Overview 

<ul>

<li class="fragment">**What is it?**  
a new, open source, interactive theorem prover 
<p>
</p>
</li>

<li class="fragment">**Where did it come from?**  
Principle Developer: **Leonardo de Moura**, Microsoft Research
<p>
</p>
</li>

<li class="fragment">**Where can one get it?**  
<center>http://leanprover.github.io</center>
<p>
</p>
</li>

</ul>

---

### Perspective

Some popular software with substantial mathematical libraries:
+ **Mizar** (set theory)
+ **ACL2** (primitive recursive arithmetic)
+ **HOL4** (simple type theory)
+ **Isabelle** (simple type theory)
+ **HOL light** (simple type theory)
+ **PVS** classical dependent type theory)
+ **Coq** (constructive dependent type theory)
+ **Adga** (constructive dependent type theory)    

<p class="fragment">
Why develop (or adopt) another proof assistant?
</p>

---

### Motivation

Lean is...

+ a **fresh start** incorporating the best ideas from existing systems
   
+ a **hybrid interactive/automated** system, being both
  - an interactive theorem prover with powerful automation
  - an automated reasoning tool capable of producing detailed proofs
    
+ a **verified mathematical library**
 
+ a **programming environment** for
  - *computing* with objects using a precise formal semantics
  - *reasoning* about the results of computation
  - *creating* proof-producing automations

---

### Motivation

Lean can

+ verify mathematics  

+ verify hardware, software, and hybrid systems  

+ support reasoning and exploration  

+ support formal methods in education  

+ bring formal methods to the masses

---

### History of Lean

+ **2013** Project Started
 
+ **2015** Lean 2 announced
 
+ **2017** Lean 3 now available  
 
+ **2018** standard library and automation still under development  
 
(HoTT development is ongoing *in Lean 2 only*)

---

### Notable Features of Lean

+ written in C++ with **multi-core support**  
 
+ **small trusted** kernel with independent type checkers  

+ based on **constructive type theory** but supports **classical logic**  

+ supports **type class inference**

+ compiles structural/nested/mutual/well-founded recursive definitions down to **primitives**

+ **bytecode interpreter** for evaluating computable
definitions

+ supports **metaprogramming** via monadic interface to Lean internals

+ **profiler**, **debugger**, **simplifier** with conditional rewriting

+ enthusiastic, talented **people** involved

---

### People of Lean
<span style="color:#e49436">**Code base:**</span> Leonardo de Moura, Gabriel Ebner, Sebastian Ullrich, Jared Roesch, Daniel Selsam

<span style="color:#e49436">**Libraries:**</span> Jeremy Avigad, Floris van Doorn, Leonardo de Moura, Robert Lewis, Gabriel Ebner, Johannes Hölzl, Mario Carneiro

<span style="color:#e49436">**Contributors:**</span>  Soonho Kong, Jakob von Raumer, Assia Mahboubi, Cody Roux, Parikshit Khanna, Ulrik Buchholtz, Favonia (Kuen-Bang Hou), Haitao Zhang, Jacob Gross, Andrew Zipperer, Joe Hurd
