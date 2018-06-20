#print "Chapter 9. Structures and Records

We've seen that Lean's foundational system includes inductive types. 

We've noted the remarkable fact that it is possible to construct a substantial 
edifice of math based on just the type universes, Pi types, and inductive types; 
everything else follows from these. 

Lean's std lib contains many instances of inductive types (e.g., nat, prod, list); 
even the logical connectives are defined using inductive types.

Remember, a non-recursive inductive type that contains only one constructor is called 
a *structure* or *record*. The product type is a structure, as is the dependent product 
type, that is, the *Sigma type*. 

In general, whenever we define a structure `S`, we usually define *projection* functions 
that allow us to 'destruct' each instance of `S` and retrieve the values stored in its 
fields. The functions `prod.pr1` and `prod.pr2`---the first and second elements of a 
pair---are examples.

When writing programs or formalizing math, it's common to define structures containing 
many fields. The `structure` command, available in Lean, provides infrastructure to 
support this process. When we use this command, Lean automatically generates all projection 
functions. 

The `structure` command also allows us to define new structures based on previously defined 
ones. Moreover, Lean provides convenient notation for instances of a given structure."


#print "===========================================
Section 9.1. Declaring Structures

The structure command is essentially a 'front end' for defining inductive data types. 
Every `structure` declaration introduces a namespace with the same name. 

The general form is as follows:

    structure <name> <parameters> <parent-structures> : Sort u :=
      <constructor> :: <fields>

Most parts are optional. Here is an example:"
namespace Sec_9_1
  structure point (α : Type) := mk :: (x: α) (y: α)
  -- Values of type point are created by instantiating the point structure with 
  -- the mk constructor, as follows:
  #reduce point.mk 2 4
  -- ...and here are the projections:
  #reduce point.x (point.mk 2 4)  #reduce point.y (point.mk 2 4)

  --The structure command also generates some useful recursors and theorems, e.g.,

  -- point introduction
  #check point           -- point: Type → Type

  -- point elimination
  #check @point.rec_on   --   Π {α: Type} {C: point α → Sort u_1} (p : point), 
                         --     (Π (x y : α), C {x := x, y:= y}) → C p
  -- the projections
  #check @point.x         -- Π {α : Type}, point α → α                         
  #check @point.y         -- Π {α : Type}, point α → α                         

  -- you can obtain a complete list of the generated constructions using `#print prefix`
  #print prefix Sec_9_1.point

  -- Above we constructed a point and then took projections, like this:
  #reduce point.mk 2 4  #reduce point.x (point.mk 2 4)  #reduce point.y (point.mk 2 4)
  -- We could have opened point and then dropped "point." from each of these.
  open point
  #reduce mk 2 4
  #reduce x (mk 2 4)  -- result: 2  ...seems a bit cryptic if you're not used to it
  #reduce (mk 2 4).x  -- result: 2  ...using instead the . style like in oop
  #reduce (mk 2 4).y  -- result: 4

  example (α: Type) (a b : α) : x (mk a b) = a := rfl
  theorem example_2nd_projection (α: Type) (a b : α) : y (mk a b) = b := rfl
  #print example_2nd_projection
  
end Sec_9_1


#print "==========================================="
#print "Section 9.2. Objects"
#print " "

namespace Sec_9_2

end Sec_9_2


#print "==========================================="
#print "Section 9.3. Inheritance"
#print " "

namespace Sec_9_3

end Sec_9_3


