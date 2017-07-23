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
    constant empty : Π {α : Type u}, vec α 0
    constant cons : Π {α : Type u} {n : ℕ}, α → vec α n → vec α (n + 1)
    constant append : Π {α : Type u} {n m : ℕ},
                    vec α n → vec α m → vec α (n + m)
    constant add : Π {α : Type u} {n : ℕ}, vec α n → vec α n → vec α n
    constant reverse : Π {α : Type u} {n : ℕ}, vec α n → vec α n
  end vec

  variable α : Type u
  variable v : vec α 10
  variable w : vec α 5
  variable z : vec α 5

-- (partial application types)
  #check @vec.append α 10 5 v         -- vec α 5 → vec α (10 + 5)
  #check @vec.append α 10 _ v         -- vec α ?M_1 → vec α (10 + ?M_1)

  #check vec.append v w               -- vec α (10 + 5)
  #check vec.add w z                  -- vec α 5
  #check vec.add v (vec.append w z)   -- vec α 10

end exercise3

/- 4. Similarly, declare a constant =matrix= so that =matrix α m n= could represent the type 
      of =m= by =n= matrices. Declare some constants to represent functions on this type, 
      such as matrix addition and multiplication, and (using =vec=) multiplication of a 
      matrix by a vector. Once again, declare some variables and check some expressions 
      involving the constants that you have declared.  -/
namespace exercise4
  universe u
  constant matrix : Type u → ℕ → ℕ → Type u

  namespace matrix 
    constant empty : Π {α : Type u}, matrix α 0 0
    constant plus : Π {α : Type u} {m n : ℕ}, matrix α m n → matrix α m n → matrix α m n
    constant prod : Π {α : Type u} {i k j : ℕ}, matrix α i k → matrix α k j → matrix α i j
  end matrix

  variables α β : Type u
  variables M1 M2 : matrix α 2 3
  variable M3 : matrix α 3 4
  variable N3 : matrix β 3 4

  #check matrix.plus M1 M2        -- matrix α 2 3
  #check matrix.prod M2 M3        -- matrix α 2 4

  -- #check matrix.plus M1 M3      -- (dimensions not compatible with plus)
  -- #check matrix.prod M1 M2      -- (dimensions not compatible with prod)
  -- #check matrix.prod M2 N3      -- (expected `matrix α 3 ?` but `N3 : matrix β 3 4`)

end exercise4
