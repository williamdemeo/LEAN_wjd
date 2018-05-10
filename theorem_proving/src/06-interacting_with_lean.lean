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
  -- Lean's parser is extensible, which is to say, we can define new notation.
  -- If declared in a namespace, the notation is only available when the namespace is open.
  namespace hide₁
    notation `[` a `**` b `]` := a * b + 1   -- defines a binary notation for mult and add one. 
    def mul_square (a b : ℕ) := a * a * b * b
    infix `<*>`:50 := mul_square   -- declares an infix operator, with precedence 50, 
                                   -- which associates to the left (with left-binding power 50) 
                                   -- `infixr` defines notation which associates to the right
    #check [2 ** 3]
    #reduce [2 ** 3]
    #reduce 2 <*> 3
  end hide₁

  -- Temporary notation is declared with `local`; such notation is available in the current file, 
  -- within the current ``namespace`` or ``section``, if you are in one.
  namespace hide₂
    local notation `[` a `**` b `]` := a * b + 1
    local infix `<*>`:50 := λ a b : ℕ, a * a * b * b
    variables a b : ℕ
    #check [a ** b]
    #reduce [4 ** 5]
    -- Lean's core library declares the left-binding powers of a number of common symbols.
    /- ``https://github.com/leanprover/lean/blob/master/library/init/core.lean`` -/
  end hide₂

  -- You can direct the pretty-printer to suppress notation with `set_option pp.notation false`. 
  -- You can also declare notation for input purposes only with ``[parsing_only]`` attribute.
  namespace hide₃
    notation [parsing_only] `[` a `**` b `]` := a * b + 1  -- QUESTION: what does this do?
    variables a b : ℕ
    #check [a ** b]
    #reduce [4 ** 5]
  end hide₃

  -- Declaring parameters in a section makes it possible to define local notation that depends 
  -- on those parameters. Below, as long as ``m`` is fixed, we can write ``a ≡ b`` for 
  -- equivalence mod ``m``. When the section is closed, the dependence on ``m`` becomes explicit, 
  -- and the notation ``a ≡ b`` is no longer valid.
  namespace my_int
    def dvd (m n : ℤ) : Prop := ∃ k, n = m * k
    instance : has_dvd int := ⟨my_int.dvd⟩
    @[simp]
    theorem dvd_zero (n : ℤ) : n ∣ 0 := ⟨0, by simp⟩
    theorem dvd_intro {m n : ℤ} (k : ℤ) (h : n = m * k) : m ∣ n := ⟨k, h⟩
  end my_int
  section mod_m
    open my_int
    parameter (m : ℤ)
    variables (a b c : ℤ)
    definition mod_equiv := (m ∣ b - a)
    local infix ≡ := mod_equiv
    theorem mod_refl : a ≡ a := show m ∣ a - a, by simp
    theorem mod_symm (h : a ≡ b) : b ≡ a := 
      by cases h with c hc; apply dvd_intro (-c); simp [eq.symm hc]
    theorem mod_trans (h₁ : a ≡ b) (h₂ : b ≡ c) : a ≡ c :=
      begin
        cases h₁ with d hd, cases h₂ with e he, 
        apply dvd_intro (d + e),
        simp [mul_add, eq.symm hd, eq.symm he]
      end
  end mod_m
  #check (mod_refl : ∀ (m a : ℤ), mod_equiv m a a)
  #check (mod_symm : ∀ (m a b : ℤ), mod_equiv m a b → mod_equiv m b a)
  #check (mod_trans :  ∀ (m a b c : ℤ), mod_equiv m a b → mod_equiv m b c → mod_equiv m a c)
end Sec_6_6 

#print "========================================"
#print "Section 6.7. Coercions"
#print " "

namespace Sec_6_7 

  -- In Lean, the type of natural numbers, `nat`, is different from the type of integers, `int`. 
  -- But `int.of_nat` embeds the nats in the ints, meaning we can view any nat as an int.
  -- Lean has mechanisms to detect and insert *coercions* of this sort.
  variables m n : ℕ
  variables i j : ℤ
  #check i + m      -- i + ↑m : ℤ       -- the output shows the coercion by printing an arrow, 
  #check i + m + j  -- i + ↑m + j : ℤ   -- which is notation for the function ``coe``
  #check i + m + n  -- i + ↑m + ↑n : ℤ  -- type unicode up arrow with ``\u`` or use `coe` instead

  -- When the order of arguments is different, you have to insert the coercion manually, 
  -- because Lean does not recognize the need for coercion until it has parsed earlier arguments.
  -- #check m + i  -- is an error
  #check ↑m + i        -- ↑m + i : ℤ
  #check ↑(m + n) + i  -- ↑(m + n) + i : ℤ
  #check ↑m + ↑n + i   -- ↑m + ↑n + i : ℤ
  -- Lean allows various kinds of coercions using type classes (see Ch. 10)

end Sec_6_7 

#print "========================================"
#print "Section 6.8. Displaying Information"
#print " "

/- There are a number of ways in which you can query Lean for information about its current 
   state and the objects and theorems that are available in the current context. 
   We have already seen 2: `#check` and `#reduce` 

   `#check` is often used with `@`, which makes all arguments to a thm or def explicit. 

   You can also use `#print` to get information about any identifier. 
   If it's a definition or theorem, Lean prints the type of the symbol, and its definition. 
   If it's a constant or an axiom, Lean indicates that fact, and shows the type. -/

namespace Sec_6_8 
   -- examples with equality
   #check eq
   #check @eq
   #check eq.symm
   #check @eq.symm
   #print eq.symm

   -- examples with and
   #check and
   #check and.intro
   #check @and.intro

   -- a user-defined function
   def foo {α : Type} (x : α) : α := x
   #check foo
   #check @foo
   #reduce foo
   #reduce (foo nat.zero)
   #print foo

   -- There are other useful ``#print`` commands. 
   -- #print "#print notation"
   -- #print notation
   #print "----------------------------------------------------"
   #print "#print notation + *"
   #print notation + * -
   #print " "
   #print "----------------------------------------------------"
   #print "#print axioms"
   #print axioms
   #print " "
   #print "----------------------------------------------------"
   #print "#print options"
   #print options
   #print " "
   #print "----------------------------------------------------"
     -- #print "#print prefix nat"  (TOO MUCH OUTPUT... 
     -- #print prefix nat             ...but interesting to look at how much is defined for nat;
     -- #print " "                    uncomment these lines to see.)
     -- #print "----------------------------------------------------"
   #print "#print prefix nat.le"
   #print prefix nat.le
   #print " "
   #print "----------------------------------------------------"
   #print "#print classes"
   #print classes
   #print " "
   #print "----------------------------------------------------"
   #print "#print instances ring"
   #print instances ring
   #print " "
   #print "----------------------------------------------------"
   #print "#print fields ring"
   #print fields ring
   #print " "
   #print "----------------------------------------------------"
   #print "#print group"
   #print group    -- recognizes that a group is a structure and so print the fields as well.
   #print " "
   #print "----------------------------------------------------"
   #print "#print list.append"
   #print list.append -- same as `#print definition list.append`
   #print " "
   #print "----------------------------------------------------"
   #print "#print notation +"
   #print notation + -- same as `#print +`
   #print " "
   #print "----------------------------------------------------"
   #print "#print nat"
   #print nat    -- same as `#print inductive nat`
   #print " "
end Sec_6_8 

#print "========================================"
#print "Section 6.9. Setting Options"
#print " "

namespace Sec_6_9 
  -- Lean maintains some internal variables that can be set to control its behavior. 
  --   `set_option <name> <value>`
  -- One useful family of options controls the way Lean's *pretty-printer* displays terms. 
  -- The following options take an input of true or false:
  set_option pp.implicit true  -- display implicit arguments
  set_option pp.universes true -- display hidden universe parameters
  set_option pp.coercions true -- show coercions
  -- set_option pp.notation false -- display output using defined notations
  -- set_option pp.numerals false -- (what does this do?)
  set_option pp.beta true      -- beta reduce terms before displaying them
  -- set_option pp.all true       -- carries out these settings all at once, whereas 
  #check 2 + 2 = 4
  #reduce (λ x, x + 2) = (λ x, x + 3)
  #check (λ x, x + 1) 1
  set_option pp.all false      -- reverts to the previous values.
  #check 2 + 2 = 4
  #reduce (λ x, x + 2) = (λ x, x + 3)
  #check (λ x, x + 1) 1

  /- Pretty printing additional information is often very useful when you are debugging a proof, 
     or trying to understand a cryptic error message. Too much information can be overwhelming, 
     though, and Lean's defaults are generally sufficient for ordinary interactions.-/
  -- By default, the pretty-printer does not reduce applied lambda-expressions, but 
  -- this is sometimes useful. The ``pp.beta`` option controls this feature.
  set_option pp.beta true
  #check (λ x, x + 1) 1
  set_option pp.beta false
  #check (λ x, x + 1) 1
end Sec_6_9 

#print "========================================"
#print "Section 6.10. Elaboration Hints"
#print " "

namespace Sec_6_10

/- When you ask Lean to process an expression, like `λ x y z, f (x + y) z`, you are leaving 
   information implicit. For example, the types of `x`, `y`, and `z` have to be inferred 
   from the context, the notation ``+`` may be overloaded, and there may be implicit arguments 
   to `f` that need to be filled in as well. Moreover, we will see in Ch 10 that some implicit 
   arguments are synthesized by a process known as *type class resolution*. And we have also 
   already seen in the last chapter that some parts of an expression can be constructed by the 
   tactic framework. -/

/- Inferring some implicit arguments is straightforward. For example, suppose a function `f` 
   has type `Π {α : Type}, α → α → α` and Lean is trying to parse the expression `f n`, 
   where `n` can be inferred to have type `nat`. Then it is clear that the implicit argument `α` 
   has to be `nat`. However, some inference problems are *higher order*. For example, the 
   substitution operation for equality, `eq.subst`, has the following type: -/
   
   -- eq.subst : ∀ {α : Sort u} {p : α → Prop} {a b : α}, a = b → p a → p b

   -- Now suppose we are given `a b : ℕ` and `h₁ : a = b` and `h₂ : a * b > a`. 
   -- Then, in the expression `eq.subst h₁ h₂`, `P` could be any of the following:
   -- -  `λ x, x * b > x`
   -- -  `λ x, x * b > a`
   -- -  `λ x, a * b > x`
   -- -  `λ x, a * b > a`

   /- In other words, our intent may be to replace either the first or second `a` in `h₂`, 
      or both, or neither. Similar ambiguities arise in inferring induction predicates, 
      or inferring function arguments. Even second-order unification is known to be undecidable. 
      Lean therefore relies on heuristics to fill in such arguments, and when it fails to guess 
      the right ones, they need to be provided explicitly. -/

   /- To make matters worse, sometimes definitions need to be unfolded, and sometimes expressions 
      need to be reduced according to the computational rules of the underlying logical framework.       Again, Lean has to rely on heuristics to determine what to unfold or reduce, and when. -/

   /- There are attributes, however, that can be used to provide hints to the elaborator. 
      One class of attributes determines how eagerly definitions are unfolded: 
      - constants can have attributes `[reducible]`, `[semireducible]`, or `[irreducible]`. 
      - Definitions are marked `[semireducible]` by default. 
      - A definition with the `[reducible]` attribute is unfolded eagerly; 
        if you think of a definition are serving as an abbreviation, this attribute is appropriate.
      - The elaborator avoids unfolding definitions with the `[irreducible]` attribute. 
        Theorems are marked `[irreducible]` by default, because typically proofs are not 
        relevant to the elaboration process. -/

   /- These attributes are only hints to the elaborator. When checking an elaborated term for 
      correctness, Lean's kernel will unfold whatever definitions it needs to unfold. 
      Again, attributes can be made `local` (in effect only in the current section/file). -/

   /- Lean also has a family of attributes that control the elaboration strategy. 
      A definition or theorem can be marked `[elab_with_expected_type]`, `[elab_simple]`. or 
      `[elab_as_eliminator]`. When applied to a definition `f`, these bear on elaboration 
      of an expression `f a b c ...` in which `f` is applied to arguments. With the default 
      attribute, `[elab_with_expected_type]`, the arguments `a`, `b`, `c`, ... are elaborating 
      using information about their expected type, inferred from `f` and the previous arguments. 
      In contrast, with `[elab_simple]`, the arguments are elaborated from left to right without 
      propagating information about their types. The last attribute, `[elab_as_eliminator]`, 
      is commonly used for eliminators like recursors, induction principles, and `eq.subst`. 
      It uses a separate heuristic to infer higher-order parameters. -/

   /- Again, attributes can assigned and reassigned after an object is defined, and you can use 
      the `local` modifier to limit their scope. Using the `@` symbol instructs the elaborator 
      to use the `[elab_simple]` strategy; the idea is that, when you provide the tricky 
      parameters explicitly, you want the elaborator to weigh that information heavily. In fact, 
      Lean offers an alternative annotation, `@@`, which leaves parameters before the first 
      higher-order parameter explicit. For example, `@@eq.subst` leaves the type of the equation 
      implicit, but makes the context of the substitution explicit.  -/
end Sec_6_10

#print "========================================"
#print "Section 6.11. Using the Library"
#print " "

namespace Sec_6_11
  /- To use Lean effectively you will inevitably need to make use of definitions and theorems 
     in the library. Recall that `import` at the beginning of a file imports previously compiled 
     results from other files, and that importing is transitive. But opening a namespace, which 
     provides shorter names, does not carry over. In each file, you need to open the namespaces 
     you wish to use. -/

  /- In general, it's important to be familiar with the library and its contents, so you know 
     what theorems, definitions, notations, and resources are available to you. Below we will 
     see that Lean's editor modes can also help you find things you need, but studying the 
     contents of the library directly is often unavoidable. Lean's standard library can be 
     found online, on github:

     https://github.com/leanprover/lean/tree/master/library

     You can see the contents of the directories and files using github's browser interface. 
     If you have installed Lean on your own computer, you can find the library in the `lean` 
     folder, and explore it with your file manager. Comment headers at the top of each file 
     provide additional information.

     Lean's library developers follow general naming guidelines to make it easier to guess the 
     name of a theorem you need, or to find it using tab completion in editors with a Lean mode 
     that supports this, which is discussed in the next section. Identifiers are generally 
     `snake_case`, which is to say, they are composed of words written in lower case separated 
     by underscores. For the most part, we rely on descriptive names. Often the name of theorem 
     simply describes the conclusion: -/
    open nat

    #check succ_ne_zero
    #check @mul_zero
    #check @mul_one
    #check @sub_add_eq_add_sub
    #check @le_iff_lt_or_eq

  -- If only a prefix of the description is enough to convey meaning, the name may be even shorter.
    #check @neg_neg
    #check pred_succ

  /- Sometimes, to disambiguate the name of theorem or better convey the intended reference, 
     it is necessary to describe some of the hypotheses. The word "of" is used to separate 
     these hypotheses: -/
    #check @nat.lt_of_succ_le
    #check @lt_of_not_ge
    #check @lt_of_le_of_ne
    #check @add_lt_add_of_lt_of_le

  -- Sometimes the word "left" or "right" is helpful to describe variants of a theorem.
    #check @add_le_add_left
    #check @add_le_add_right

  -- We can also use the word "self" to indicate a repeated argument:
    #check mul_inv_self
    #check neg_add_self

  /- Remember, identifiers in Lean can be organized into hierarchical namespaces. For example, 
     the theorem named `lt_of_succ_le` in the namespace `nat` has full name `nat.lt_of_succ_le`, 
     but the shorter name is made available by the command `open nat`. We will see later that 
     defining structures and inductive data types in Lean generates associated operations, and 
     these are stored in a namespace with the same name as the type under definition. 
     For example, the product type comes with the following operations: -/
    #check @prod.mk  -- to construct a pair
    #check @prod.fst -- first projection
    #check @prod.snd -- second projection
    #check @prod.rec -- provides another mechanism for defining functions on a product 
                     -- in terms of a function on the two components. 

  /- Names like `prod.rec` are *protected*, which means that one has to use the full name even 
     when the `prod` namespace is open. -/

  -- With the propositions as types correspondence, logical connectives are also instances of 
  -- inductive types, and so we tend to use dot notation for them as well:
    #check @and.intro
    #check @and.elim
    #check @and.left
    #check @and.right
    #check @or.inl
    #check @or.inr
    #check @or.elim
    #check @exists.intro
    #check @exists.elim
    #check @eq.refl
    #check @eq.subst

    -- compare prod.mk to and.intro:
    #check @prod.mk
    #check @and.intro

end Sec_6_11

