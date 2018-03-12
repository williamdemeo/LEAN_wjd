/- Exercises

1. Define the function ``Do_Twice``, as described
   in [Introducing Definitions](#introducing-definitions). 
-/
def double : ℕ → ℕ := λ x, x + x
def square : ℕ → ℕ := λ x, x * x
def do_twice : (ℕ → ℕ) → ℕ → ℕ := λ f x, f (f x)

/- Try defining `Do_Twice : ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → (ℕ → ℕ)`
   which applies its argument twice, so that Do_Twice do_twice is a function that 
   applies its input four times. Then evaluate Do_Twice do_twice double 2. -/

def Do_Twice : ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → (ℕ → ℕ) := 
  λ (F : (ℕ → ℕ) → (ℕ → ℕ)) (f : ℕ → ℕ) (x : ℕ), f (f x)

#check Do_Twice

#eval Do_Twice do_twice double 2

/-
2. Define the functions ``curry`` and ``uncurry``, as described
   in [Introducing Definitions](#introducing-definitions). -/

def curry (α β γ : Type) (f : α × β → γ) : α → β → γ := λ x y, f(x,y)

def uncurry (α β γ : Type) (f : α → β → γ) : α × β → γ := λ p, f p.1 p.2


/-

3. Above, we used the example ``vec α n`` for vectors of elements of type ``α``
   of length ``n``. Declare a constant ``vec_add`` that could represent a
   function that adds two vectors of natural numbers of the same length, and a
   constant ``vec_reverse`` that can represent a function that reverses its
   argument. Use implicit arguments for parameters that can be inferred. Declare
   some variables and check some expressions involving the constants that you
   have declared. 

4. Similarly, declare a constant ``matrix`` so that ``matrix α m n`` could
   represent the type of ``m`` by ``n`` matrices. Declare some constants to
   represent functions on this type, such as matrix addition and multiplication,
   and (using ``vec``) multiplication of a matrix by a vector. Once again,
   declare some variables and check some expressions involving the constants
   that you have declared. 

-/
