#print "
Section 10.5. Managing Type Class Inference
-------------------------------------------"

  #print "In the Emacs `lean-mode`, tab completion works in `set_option`, to help you 
  find suitable options.

  As noted above, the type class instances in a given context represent a Prolog-like 
  program, which gives rise to a backtracking search. Both the efficiency of the program 
  and the solutions that are found can depend on the order in which the system tries the 
  instance. Instances that are declared last are tried first. Moreover, if instances are 
  declared in other modules, the order in which they are tried depends on the order in 
  which namespaces are opened. Instances declared in namespaces which are opened later 
  are tried earlier.

  You can change the order that type classes instances are tried by assigning them a 
  *priority*. When an instance is declared, it is assigned a priority value 
  `std.priority.default`, defined to be 1000 in module `init.core` in the standard library. 
  You can assign other priorities when defining an instance, and you can later change the 
  priority with the `attribute` command."


class foo := (a: nat) (b: nat)
  
@[priority std.priority.default+1] 
instance i1 : foo := ⟨1, 1⟩ 

instance i2 : foo := ⟨2, 2⟩ 

example : foo.a = 1 := rfl

@[priority std.priority.default+20]
instance i3 : foo := ⟨3, 3⟩ 

example : foo.a = 3 := rfl

attribute [instance, priority 10] i3

example : foo.a = 1 := rfl

attribute [instance, priority std.priority.default-10] i1

example : foo.a = 2 :=rfl

