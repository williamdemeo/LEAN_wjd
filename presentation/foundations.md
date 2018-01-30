  
### Logical Foundations of Lean

1. based on the 
   <span style="color:#e49436">Calculus of Inductive Constructions</span>
   with:    
   - a hierarchy of **universes** with a type `Prop` at bottom
   - **dependent function types** (Pi types)
   - **inductive types** (à la Dybjer)

2. semi-constructive axioms and constructions:
  - **quotient types** (implies function extensionality)  
  - **propositional extensionality**

3. A single classical axiom:  
  - **choice**

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
  ```coq
  Prop, Type 0, Type 1, Type 2, . . .
  ```

+ `Prop` is *impredicative* and definitionally *proof irrelevant*.   
  That is, if 
  ```coq
  p : Prop, s : p, t : p
  ```
  then `s` and `t` are definitionally equal.

---

### Logical Foundations

Lean supports **dependent function types**, as in $\Pi\limits_{x : A} B_x$

```
  Π x : α . β x
```
with the usual "β-reduction" rule:   
```
  (λx.t) s = [s / x] t
```
**Example:** 

```coq
universe u
constant vec : Type u → ℕ → Type u

namespace vec
  constant empty : Π α : Type u, vec α 0
  constant cons :
    Π (α : Type u) (n : ℕ), α → vec α n → vec α (n + 1)
  constant append :
    Π (α : Type u) (n m : ℕ),  vec α m → vec α n → vec α (n + m)
end vec
```

---  

### Logical Foundations

+ **eta equivalence** for functions  
  `t` and `(λx.t)x` are definitionally equal

+ **let definitions**  
  ```coq
  let x := s in t
  ```
  with the expected reduction rule

---

### Logical Foundations

Lean implements **inductive families** with **primitive recursors** with the
expected computation rules.

```coq
inductive vector (α : Type u) : N → Type u
| nil : vector 0
| cons {n : N} (a : α) (v : vector n) : vector (n+1)

-- this inductive defintion produces the following

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
