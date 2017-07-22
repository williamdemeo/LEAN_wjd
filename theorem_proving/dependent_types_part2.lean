#print "------------------------------------------------"
#print "Section 2.5. Local Definitions"

-- Lean allows you to introduce "local" definitions using the let construct.

/- The expression let `a := t1 in t2` is definitionally equal to the result of 
   replacing every occurrence of `a` in `t2` by `t1`. -/
namespace page20
  #check let y := 2 + 2 in y * y                     -- ℕ
  #reduce let y := 2 + 2 in y * y                    -- 16
  def t (x : ℕ) : ℕ := let y := x + x in y * y
  #reduce t 2                                        -- 16
end page20


#print "------------------------------------------------"
#print "Section 2.6. Variables and Sections"

-- some organizational features of Lean (not part of axiomatic framework per se)

/- Recall, the `constant` command allows us to declare new objects, which
   then become part of the global context. This can be somewhat dangerous since 
   declaring a new constant is tantamount to declaring an axiomatic extension of 
   our foundational system, and may result in inconsistency.

   This can be avoided, using implicit or explicit lambda abstraction
   in our definitions to declare such objects "locally".
-/
namespace page21

  def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ := g (f x)

  def do_twice (α : Type) (h : α → α) (x : α) : α := h (h x)

  /- Repeating declarations in this way can be tedious, however. Lean provides us with
     the `variable` and `variables` commands to make such declarations look global:
  -/
  variables (α β γ : Type)
  def compose_alt (g : β → γ) (f : α → β) (x : α) : γ := g (f x)

end page21
/- The variable and variables commands look like the constant and constants commands, 
   but there is an important difference. Rather than creating permanent entities, 
   the `variables` command simply instructs Lean to insert the declared variables 
   as bound variables in definitions that refer to them. -/

/- A variable stays in scope until the end of the file we are working on, and we 
   cannot declare another variable with the same name. 

   To limit the scope of a variable, Lean provides the notion of a section:
-/

section useful
  variables (α β γ : Type)
  variables (g : β → γ) (f : α → β) (h: α → α)
  variable x : α
  def compose := g (f x)
  def do_twice := h (h x)
end useful



#print "------------------------------------------------"
#print "Section 2.7 Namespaces"

/- Lean provides us with the ability to group definitions, notation, and other 
   information into nested, hierarchical namespaces.
-/

namespace fu
  def a : ℕ :=5
  def f (x : ℕ) : ℕ := x+7

  def fa : ℕ := f a
  def ffa : ℕ := f (f a)

  #print "inside fu"
  #check a
  #check f
  #check fa
  #check ffa
  #check fu.fa
  
end fu
#print "outside the fu namespace"
-- #check a               -- error
-- #check f               -- error
#check fu.a
#check fu.ffa

open fu
#print "opened fu"
#check a
-- #check f     -- still an error because ambiguous (f was also defined above)
#check fu.f
#check ffa

/- The `open` command brings the shorter names into the current context. Often, 
   when we import a theory file, we will want to open one or more of the namespaces 
   it contains, to have access to the short identifiers, notations, and so on. 
   But sometimes we will want to leave this information hidden, for example, when 
   they conflict with identifiers and notations in another namespace we want to use. 
   Thus namespaces give us a way to manage our working environment.
-/

-- Lean groups definitions and theorems involving lists into a namespace `list`.

#check list.nil
#check list.cons
#check list.append

open list
#check nil
#check cons
#check append

-- like sections, namespaces can be nested
namespace page24
  namespace pre
    def a : ℕ := 5
    def f (x : ℕ) : ℕ := x+7
  end pre

  namespace top
    def fa : ℕ := pre.f a
    
    namespace bar
      def ffa : ℕ := pre.f (pre.f a)

      #check fa
      #check ffa
    end bar

    #check fa
    #check bar.ffa

  end top


end page24

-- Namespaces that have been closed can later be reopened, even in another file.

namespace page24
  def b : ℕ := 5
end page24

/- Namespaces and sections serve different purposes: namespaces organize data and 
   sections declare variables for insertion in theorems. -/

/- Section 2.7. output:
                inside fu
                a : ℕ
                f : ℕ → ℕ
                fa : ℕ
                ffa : ℕ
                fa : ℕ
                outside the fu namespace
                fu.a : ℕ
                fu.ffa : ℕ
                opened fu
                a : ℕ
                f : ℕ → ℕ
                ffa : ℕ
                list.nil : list ?M_1
                list.cons : ?M_1 → list ?M_1 → list ?M_1
                list.append : list ?M_1 → list ?M_1 → list ?M_1
                nil : list ?M_1
                cons : ?M_1 → list ?M_1 → list ?M_1
                append : ?M_1 → ?M_1 → ?M_1
                fa : ℕ
                ffa : ℕ
                fa : ℕ
                bar.ffa : ℕ
-/



#print "------------------------------------------------"
#print "Section 2.8 Dependent Types"

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
   Given `α : Type` and `β : α → Type`, think of β as a family of types over α. 
   We have a type `β a` for each `a : α`.  The type 
            Π x : α, β x 
   denotes the type of functions f with the property that, for each `a : α`, 
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
  universe u
  constant list : Type u → Type u   -- N.B. we don't just want `list : Type → Type`
  constant cons : Π (α : Type u), α → list α → list α
  constant nil : Π (α : Type u), list α
  constant head : Π (α : Type u), list α → list α
  constant tail : Π (α : Type u), list α → list α
  constant append : Π (α : Type u), list α → list α → list α
end page25  


  #check list
  #check @cons
  #check @nil
  #check @head
  #check @tail
  #check @append


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

/- When p is a dependent pair `(sigma.mk a b).1` and `(sigma.mk a b).2` 
   are short for `sigma.fst (sigma.mk a b)` and `sigma.snd (sigma.mk a b)`, 
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
