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
  /- The command `namespace foo` causes foo to be prepended to the name of each definition 
     and theorem until `end foo` is encountered. The command `open foo` then creates 
     temporary aliases to definitions and theorems that begin with prefix `foo`. -/

namespace Sec_6_3 
  namespace foo
    def bar : ℕ := 1
  end foo

  open foo
  #check bar
  #check foo.bar

  -- The string ``_root_`` is an explicit description of the empty prefix.
  #check add_sub_cancel
  #check nat.add_sub_cancel
  #check _root_.add_sub_cancel

  -- We can prevent the shorter alias from being created by using the ``protected`` keyword:
  namespace foo2
    protected def bar2 : ℕ := 1
  end foo2

  open foo2
  -- #check bar2 -- error
  #check foo2.bar2
  -- This is often used for names like ``nat.rec``, to prevent overloading common names.

  -- The ``open`` command admits variations. 
  -- The command
  open nat (succ add sub) -- creates aliases for only the identifiers listed. 

  -- The command
  open nat (hiding succ add sub) -- creates aliases for everything *except* the identifiers lists.

  -- The command
  open nat (renaming mul → times) (renaming add → plus) 
      (hiding succ sub) -- creates aliases for everything except ``succ`` and ``sub``, 
                        -- renaming ``nat.add`` to ``plus``, and renaming the protected 
                        -- definition ``nat.induction_on`` to ``induction_on``.
  -- The command
  export nat (succ add sub) -- creates aliases for ``succ``, ``add``, ``sub`` in the current 
                            -- namespace, so whenever the namespace is open, these are available.

end Sec_6_3 

#print "========================================"
#print "Section 6.4. Attributes"
#print " "
/- Some commands have side effects on the environment, either assigning attributes to objects 
   in the environment, defining notation, or declaring instances of type classes (Ch. 10). 
   Most of these commands have global effects---they remain in effect in the current file and any 
   file that imports it. However, we can prefix them with the ``local`` modifier, which 
   indicates that they only have effect until the current ``section`` or ``namespace`` is closed, 
   or until the end of the current file. -/

/- The next example defines divisibility on natural numbers, uses it to make the natural 
   numbers an instance (Ch. 10) of a type for which the divisibility notation ``\|`` is 
   available, and assigns the ``[simp]`` attribute. -/

    def nat.dvd (m n : ℕ) : Prop := ∃ k, n = m * k
    instance : has_dvd nat := ⟨nat.dvd⟩
    attribute [simp]
    theorem nat.dvd_refl (n : ℕ) : n ∣ n := ⟨1, by simp⟩
    example : 5 ∣ 5 := by simp  -- the simplifier proves ``5 ∣ 5`` by rewriting it to ``true``. 

   -- Lean allows the alternative annotation ``@[simp]`` before a theorem to assign the attribute:
    @[simp]
    theorem nat.dvd_refl' (n : ℕ) : n ∣ n := ⟨1, by simp⟩

   -- One can also assign the attribute any time after the definition takes place:
    theorem nat.dvd_refl'' (n : ℕ) : n ∣ n := ⟨1, by simp⟩
    attribute [simp] nat.dvd_refl

   -- In all these cases, the attribute remains in effect in any file that imports this one;
   -- But adding the ``local`` modifier restricts the scope:
    section
      local attribute [simp]
      theorem nat.dvd_refl''' (n : ℕ) : n ∣ n := ⟨1, by simp⟩
      example : 5 ∣ 5 := by simp
    end
    -- Then the following would be an error (if it weren't for the previous "global" examples):
    example : 5 ∣ 5 := by simp

   -- For another example, the ``reflexivity`` tactic makes use of objects in the environment 
   -- that have been tagged with the ``[refl]`` attribute:

    @[simp,refl]
    theorem nat.dvd_refl₄ (n : ℕ) : n ∣ n := ⟨1, by simp⟩
    example : 5 ∣ 5 := by reflexivity
   -- The scope of ``[refl]`` attribute can similarly be restricted using the ``local`` modifier.

namespace Sec_6_4 

end Sec_6_4 

#print "========================================"
#print "Section 6.5. More on Implicit Arguments"
#print " "

namespace Sec_6_5 
/- If Lean displays the type of a term ``t`` as ``Π {x : α}, β x``, the curly brackets 
   indicate that ``x`` is an *implicit argument* to ``t``. This means that whenever you 
   write ``t``, a placeholder ("hole") is inserted, so ``t`` is replaced by ``@t _``. 
   If you don't want that to happen, you have to write ``@t`` instead.

   Notice that implicit arguments are inserted eagerly. Suppose we define 
   `f (x : ℕ) {y : ℕ} (z : ℕ)`
   Then, ``f 7`` is parsed as ``f 7 _``. 

   Lean offers a weaker annotation, `{{y : ℕ}}`, which specifies that a placeholder 
   should only be added *before* a subsequent *explicit* argument. 
   This can be written as ``⦃y : ℕ⦄``, where unicode brackets are entered as ``\{{`` and ``\}}``.
   Then the expression ``f 7`` is parsed as is, whereas ``f 7 3`` is parsed as ``f 7 _ 3``.

   To illustrate the difference, consider the following example, which shows that a 
   reflexive euclidean relation is both symmetric and transitive.-/
  namespace hide₁
    variables {α : Type} (r : α → α → Prop)
    definition reflexive  : Prop := ∀ (a : α), r a a
    definition symmetric  : Prop := ∀ {a b : α}, r a b → r b a
    definition transitive : Prop := ∀ {a b c : α}, r a b → r b c → r a c
    definition euclidean  : Prop := ∀ {a b c : α}, r a b → r a c → r b c
    variable {r}
    theorem th1 (reflr : reflexive r) (euclr : euclidean r) : symmetric r :=
      assume a b : α, assume : r a b, show r b a, from euclr this (reflr _)
    theorem th2 (symmr : symmetric r) (euclr : euclidean r) : transitive r :=
      assume (a b c : α), assume (rab : r a b) (rbc : r b c), euclr (symmr rab) rbc
    -- error:
    -- theorem th3 (reflr : reflexive r) (euclr : euclidean r) : transitive r :=
    --   th2 (th1 reflr euclr) euclr
    theorem th3 (reflr : reflexive r) (euclr : euclidean r) : transitive r :=
      @th2 _ _ (@th1 _ _ reflr @euclr) @euclr

    /- The results are broken down into steps: 
       ``th1`` shows that a reflexive and euclidean relation is symmetric, 
       ``th2`` shows that a symmetric and euclidean relation is transitive. 
       ``th3`` combines the two results. But we have to manually disable the implicit 
       arguments in ``th1``, ``th2``, ``euclr``, because otherwise too many implicit 
       arguments are inserted. -/
  end hide₁
  -- The problem goes away if we use weak implicit arguments.
  namespace hide₂
    variables {α : Type} (r : α → α → Prop)
    definition reflexive  : Prop := ∀ (a : α), r a a
    definition symmetric  : Prop := ∀ ⦃a b : α⦄, r a b → r b a
    definition transitive : Prop := ∀ ⦃a b c : α⦄, r a b → r b c → r a c
    definition euclidean  : Prop := ∀ ⦃a b c : α⦄, r a b → r a c → r b c
    variable {r}
    theorem th1 (reflr : reflexive r) (euclr : euclidean r) : symmetric r :=
      assume a b : α, assume : r a b, show r b a, from euclr this (reflr _)
    theorem th2 (symmr : symmetric r) (euclr : euclidean r) : transitive r :=
      assume (a b c : α), assume (rab : r a b) (rbc : r b c), euclr (symmr rab) rbc
    theorem th3 (reflr : reflexive r) (euclr : euclidean r) : transitive r :=
      th2 (th1 reflr euclr) euclr
  end hide₂

  -- A 3rd kind of implicit argument is denoted with square brackets, `[` and `]` 
  -- This is used for type classes, as explained in Ch. 10.

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

/- There are a number of ways in which you can query Lean for information about its current 
   state and the objects and theorems that are available in the current context. 
   We have already seen 2, ``#check`` and ``#reduce``. 

   Remember ``#check`` is often used in conjunction with the ``@`` operator, which makes all 
   arguments to a theorem or definition explicit. You can also use `#print` to get information 
   about any identifier. If the identifier denotes a definition or theorem, Lean prints the 
   type of the symbol, and its definition. If it is a constant or an axiom, Lean indicates 
   that fact, and shows the type. -/

namespace Sec_6_8 
  #print group
end Sec_6_8 

#print "========================================"
#print "Section 6.9. Setting Options"
#print " "

namespace Sec_6_9 
  -- Lean maintains some internal variables that can be set to control its behavior. 
  --   `set_option <name> <value>`
  -- One useful family of options controls the way Lean's *pretty-printer* displays terms. 
  -- The following options take an input of true or false:

  -- As an example,

  set_option pp.implicit true  -- display implicit arguments
  set_option pp.universes true -- display hidden universe parameters
  set_option pp.coercions true -- show coercions
  set_option pp.notation false -- display output using defined notations
  set_option pp.numerals false -- (what does this do?)
  set_option pp.beta true      -- beta reduce terms before displaying them

  #check 2 + 2 = 4
  #reduce (λ x, x + 2) = (λ x, x + 3)
  #check (λ x, x + 1) 1

  set_option pp.all true       -- carries out these settings all at once, whereas 
  set_option pp.all false      -- reverts to the previous values.

  /- Pretty printing additional information is often very useful when you are debugging a proof, 
     or trying to understand a cryptic error message. Too much information can be overwhelming, 
     though, and Lean's defaults are generally sufficient for ordinary interactions.-/
  -- By default, the pretty-printer does not reduce applied lambda-expressions, but 
  -- this is sometimes useful. The ``pp.beta`` option controls this feature.
  set_option pp.beta true
  #check (λ x, x + 1) 1
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

