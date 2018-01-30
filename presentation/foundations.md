  
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

+ Every expression has a **type** indicating the sort of object it denotes (eg, a natural number, a data type, an assertion, a proof, etc)  

+ Lean implements the logical foundation called **dependent type theory**   

+ Specifically, **CIC** is a formal language with a small, precise set of rules governing formation of expressions


---

### Logical Foundations

#### Type Universes

+ Lean has a hierarchy of *type universes*:
  ```scala
  Sort 0, Sort 1, Sort 2, Sort 3, . . .
  ```

+ These can also be written:
  ```scala
  Prop, Type 0, Type 1, Type 2, . . .
  ```

+ `Prop` is definitionally *proof irrelevant*:  
  if
  ```scala
  p : Prop, s : p, t : p
  ```
  then `s` and `t` are definitionally equal.

---

### Logical Foundations

Lean supports **dependent function types** like $\Pi_{x : A} B(x)$

```scala
  Π (x : A) , B x
```

with the usual *β-reduction rule*:   

```scala
  (λx.t) s = [s / x] t
```
#### Example

```scala
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

<!-- ### Logical Foundations

+ **eta equivalence** for functions  
  `t` and `(λx.t)x` are definitionally equal

+ **let definitions**  
  ```scala
  let x := s in t
  ```
  with the expected reduction rule -->
<!-- 
--- -->

### Logical Foundations

Lean implements **inductive families** with **primitive recursors** having the expected computation rules.

```scala
inductive vector (α : Type u) : N → Type u
| nil : vector 0
| cons {n : N} (a : α) (v : vector n) : vector (n+1)
```

... from which Lean generates ...

```scala
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

---

### Logical Foundations

We can quotient by an arbitrary binary relation:

```scala
constant quot :
  Π {α : Sort u}, (α → α → Prop) → Sort u
constant quot.mk :
  Π {α : Sort u} (r : α → α → Prop), α → quot r
axiom quot.ind :
  ∀ {α : Sort u} {r : α → α → Prop} {β : quot r → Prop},
    (∀ a, β (quot.mk r a)) → ∀ (q : quot r), β q
constant quot.lift :
  Π {α : Sort u} {r : α → α → Prop}
    {β : Sort u} (f : α → β),
    (∀ a b, r a b → f a = f b) → quot r → β
axiom quot.sound :
  ∀ {α : Type u} {r : α → α → Prop} {a b : α},
    r a b → quot.mk r a = quot.mk r b
```
These (with eta) imply function extensionality.


---

### Logical Foundations

Propositional extensionality:

```scala
axiom propext {a b : Prop} : (a ↔ b) → a = b
```

Finally, we can introduce classical axioms...

```
axiom choice {α : Sort u} : nonempty α → α
```
...if we're willing to be non-constructive and not guarantee

(Here, nonempty α is equivalent to ∃ x : α, true.)

Diaconescu's trick gives us the law of the excluded middle as a consequence.

<font color="red">Warning!</font> Definitions that use choice to produce data are noncomputable.
