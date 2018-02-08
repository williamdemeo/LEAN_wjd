#print "------------------------------------------------"
#print "Section 2.8 Dependent Types" -- (page 16 in new ed)

/- It is clear that `cons α` should have type 
            α → list α → list α 
   But what type should `cons` itself have? A first guess might be 
            Type → α → list α → list α
   But on reflection, we see this does not make sense: the α in this expression 
   does not refer to anything, whereas it should refer to the argument of type Type. 

   In other words, assuming `α : Type` is the first argument to the function, the 
   type of the next two elements are `α` and `list α`. These types *depend* on the 
   first argument `α`. 

   This is an instance of a `Pi` type, or dependent function type. 
   If we are given `α : Type` and `β : α → Type`, then we think of β as 
   a family of types indexed by α. That is, we have a type `β a` for each `a : α`.  
   The type 
            Π x : α, β x 
   denotes the type of functions f such that, for each `a : α`, 
   `f a` is an element of `β a`.

   Note that `Π x : α, β` makes sense for any expression `β : Type`. 
   When the value of β happens to depend on x, then `Π x : α, β` denotes a 
   *dependent* function type. When β doesn't depend on x, then `Π x : α, β` 
   is the same as the type `α → β`. 

   Indeed, in dependent type theory (and in Lean), the `Pi` construction is 
   fundamental, and `α → β` is just notation for `Π x : α, β` when β doesn't 
   depend on α.
-/

namespace page25
  #print "----- page17, new ed-------------------"
  universe u
  constant list : Type u → Type u   -- N.B. we don't just want `list : Type → Type`
  constant cons : Π (α : Type u), α → list α → list α
  constant nil : Π (α : Type u), list α
  constant head : Π (α : Type u), list α → α
  constant tail : Π (α : Type u), list α → list α
  constant append : Π (α : Type u), list α → list α → list α

  #check list
  #check @cons
  #check @nil
  #check @head
  #check @tail
  #check @append

end page25  



namespace page18 --(new edition)
  universe u
  constant vec : Type u → ℕ → Type u

  namespace vec
    constant empty : Π (α : Type u), vec α 0
    constant cons : Π (α : Type u) (n : ℕ), α → vec α n → vec α (n+1)
    constant append : Π (α : Type u) (n m : ℕ), vec α n → vec α m → vec α (n+m)
  end vec
end page18

/- One more important and illustrative example of dependent types, the
   *Sigma types*, `Σ x : α, β x`, sometimes known as *dependent products*.

   `Σ x : α, β x` denotes the type of pairs `sigma.mk a b` where `a : α` and `b : β a`.
-/
    
/- Pi types Π x : α, β x generalize the notion of a function type α → β by
   allowing β to depend on α.

   Sigma types `Σ x : α, β x` generalize the cartesian product `α × β` in the same way; 
   in the expression sigma.mk a b, the type of the second element, `b : β a`, depends 
   on the first element, `a : α`.
-/

namespace page27
  #print "----- page18, new ed-------------------"
  variable α : Type
  variable β : α → Type
  variable a : α
  variable b : β a

  #check sigma.mk a b          -- (a, b) : Σ (a : α), β a
  #check (sigma.mk a b).1      -- (a, b).fst : α
  #check (sigma.mk a b).2      -- β (sigma.fst (sigma.mk a b))

  #reduce (sigma.mk a b).1
  #reduce (sigma.mk a b).2
end page27

/- `(sigma.mk a b).1` and `(sigma.mk a b).2` are short for 
   `sigma.fst (sigma.mk a b)` and `sigma.snd (sigma.mk a b)`, 
   and these reduce to a and b, respectively.
   (cf. 3rd to last line of output below)
-/

/- Section 2.8 output
                list : Type u_1 → Type u_1
                cons : Π {T : Type u_1}, T → list T → list T
                nil : Π {T : Type u_1}, list T
                head : Π {α : Type u_1} [_inst_1 : inhabited α], list α → α
                tail : Π {α : Type u_1}, list α → list α
                append : Π {α : Type u_1} [c : has_append α], α → α → α
                ⟨a, b⟩ : Σ (a : α), β a
                ⟨a, b⟩.fst : α
                ⟨a, b⟩.snd : (λ (a : α), β a) (⟨a, b⟩.fst)
                a
                b
-/
                
#print "------------------------------------------------"
#print "Section 2.9 Implicit Arguments"
/- Lean allows us to specify that this argument should, by default, be left implicit. 
   This is done by putting the arguments in curly braces. -/
namespace implicits
  universe u
  def ident {α : Type u} (x : α) := x
  variables α β : Type u
  variables (a : α) (b : β)
  #check ident
  #check ident a
  #check ident b

  /- This makes the first argument to ident implicit. Notationally, this hides the specification
     of the type, making it look as though ident simply takes an argument of any type. -/

  /- Sometimes, however, we may find ourselves in a situation where we have declared an
     argument to a function to be implicit, but now want to provide the argument explicitly. -/

  #check @id
  #check @id α
  #check @id β
  #check @id α a
  #check @id β b

  /- Notice that the first #check command now gives the type of the identifier, id, without
     inserting placeholders. Moreover, the output indicates that the first argument is 
     implicit. -/

end implicits


/- Section 2.9 output
                ident : ?M_1 → ?M_1
                ident a : α
                ident b : β
                id : Π {α : Sort u_1}, α → α
                id : α → α
                id : β → β
                id a : α
                id b : β
-/
