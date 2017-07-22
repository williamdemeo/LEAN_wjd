#print "------------------------------------------------"
#print "Section 2.10 Exercises"
/- 1. Define the function =Do_twice=, as described in Section 2.4.-/
def Do_Twice : ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → (ℕ → ℕ) :=
                 λ (f: (ℕ → ℕ) → (ℕ → ℕ)) (g: ℕ → ℕ), f (f g)

/- 2. Define the functions =curry= and =uncurry=, as described in Section 2.4. -/
  def curry (α β γ : Type) (f : α × β → γ) : α → β → γ := 
         λ (x : α) (y : β), f (x, y)

  def uncurry (α β γ : Type) (f : α → β → γ) : α × β → γ :=
         λ (p : α × β), f p.1 p.2


/- 3. We used the example =vec α n= for vectors of elements of type =α= of length =n=. 
      Declare a constant =vec_add= that could represent a function that adds two vectors 
      of natural numbers of the same length, and a constant =vec_reverse= that can represent 
      a function that reverses its argument. Use implicit arguments for parameters that can 
      be inferred. Declare some variables and check some expressions involving the constants 
      that you have declared. -/

namespace exercise3
  universe u
  constant vec : Type u → ℕ → Type u

  namespace vec
    constant empty : Π (α : Type u), vec α 0
    constant cons : Π (α : Type u) (n : ℕ), α → vec α n → vec α (n + 1)
    constant append : Π (α : Type u) (n m : ℕ),
                    α → vec α n → vec α m → vec α (n + m)
    constant add : Π (α : Type u) (n : ℕ), α → vec α n → vec α n → vec α n
    constant reverse : Π (α : Type u) (n : ℕ), α → vec α n → vec α n
  end vec

end exercise3

/- 4. Similarly, declare a constant =matrix= so that =matrix α m n= could represent the type 
      of =m= by =n= matrices. Declare some constants to represent functions on this type, 
      such as matrix addition and multiplication, and (using =vec=) multiplication of a 
      matrix by a vector. Once again, declare some variables and check some expressions 
      involving the constants that you have declared.  -/
