-- 6. Interacting with Lean

/- Not all of the information in this section will be useful right away. 
   Skim this section to get a sense of Lean's features, and return later, as necessary. -/

#print "========================================"
#print "Section 6.1. Importing Files"
#print " "

namespace Sec_6_1 
  /- When Lean starts, it automatically imports the contents of the library init folder, 
     which includes a number of fundamental definitions and constructions. If you want to 
     use additional files, they need to be imported manually. 

     The command `import foo bar.baz.blah` imports the files `foo.lean` and `bar/baz/blah.lean`,
     where the descriptions are interpreted relative to the Lean search path. 

     One can also specify imports relative to the current directory; for example,
     `import .foo ..bar.baz` tells Lean to import `foo.lean` from the current directory 
     and `bar/baz.lean` relative to the parent of the current directory. -/



end Sec_6_1 

#print "========================================"
#print "Section 6.2. More on Sections"
#print " "
namespace Sec_6_2 
  /- The `section` command makes it possible not only to group together elements of a 
     theory that go together, but also to declare variables that are inserted as arguments 
     to theorems and definitions, as necessary. Remember that the point of the variable 
     command is to declare variables for use in theorems, as in the following example: -/

  section
    variables x y : ℕ

    def double := x + x
    #check double y
    #check double (2 * x)

    theorem t₁ : double (x + y) = double x + double y :=
    by simp [double]
  end

  /- Note that double does not have y as argument. Variables are only included in 
     declarations where they are actually mentioned. -/

end Sec_6_2 

#print "========================================"
#print "Section 6.3. More on Namespaces"
#print " "

namespace Sec_6_3 

end Sec_6_3 

#print "========================================"
#print "Section 6.4. Attributes"
#print " "

namespace Sec_6_4 

end Sec_6_4 

#print "========================================"
#print "Section 6.5. More on Implicit Arguments"
#print " "

namespace Sec_6_5 

end Sec_6_5 

#print "========================================"
#print "Section 6.6. Notation"
#print " "

namespace Sec_6_6 

end Sec_6_6 

#print "========================================"
#print "Section 6.7. Coercions"
#print " "

namespace Sec_6_7 

end Sec_6_7 

#print "========================================"
#print "Section 6.8. Displaying Information"
#print " "

namespace Sec_6_8 

end Sec_6_8 

#print "========================================"
#print "Section 6.9. Setting Options"
#print " "

namespace Sec_6_9 

end Sec_6_9 

#print "========================================"
#print "Section 6.10. Elaboration Hints"
#print " "

namespace Sec_6_10

end Sec_6_10

#print "========================================"
#print "Section 6.11. Using the Library"
#print " "

namespace Sec_6_11

end Sec_6_11

