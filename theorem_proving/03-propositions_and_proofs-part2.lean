#print "  "
#print "==========================================="
#print "Section 3.4 Introducing Auxiliary Subgoals"
#print "  "
/- This is a good place to introduce another device Lean offers to help structure long proofs,
   namely, the have construct, which introduces an auxiliary subgoal in a proof. Here is a
   small example, adapted from the last section: -/

namespace Sec_3_4
  variables p q : Prop
  
  theorem and_swap (h : p ∧ q) : q ∧ p :=
    have hp : p, from and.elim_left h,
    have hq : q, from and.elim_right h,
    show q ∧ p, from  and.intro hq hp

  /- Lean also supports a structured way of reasoning backwards from a goal, which models
     the "suffices to show" construction in ordinary mathematics. The next example simply
     permutes that last two lines in the previous proof. -/

  theorem and_swap' (h : p ∧ q) : q ∧ p :=
    have hp : p, from and.elim_left h,
    suffices hq : q, from and.intro hq hp,
    show q, from and.elim_right h

  
  #check and_swap'

end Sec_3_4


#print "  "
#print "====================================="
#print "Section 3.5 Classical Logic"
#print "  "

namespace page42

  /- The constructive "or" is very strong: asserting p ∨ q amounts to knowing
     which is the case. If RH represents the Riemann hypothesis, a classical 
     mathematician is willing to assert RH ∨ ¬RH, even though we cannot yet 
     assert either disjunct. -/

  open classical 

  --variable p : Prop
  #check λ (p : Prop), em p            -- p ∨ ¬p

end page42


namespace page43

  /- One consequence of the law of the excluded middle is the principle of double-negation
     elimination: -/
  open classical 

  theorem dne {p : Prop} (h : ¬¬p) : p :=
    or.elim (em p)
      (assume hp : p, hp)
      (assume hnp : ¬p, absurd hnp h)

  #check @dne
  /- double-negation elimination allows one to carry out a proof by contradiction, 
     something which is not always possible in constructive logic. -/


end page43

/- Exercise: prove the converse of dne, showing that em can be proved from dne. -/
namespace exer
  variable p : Prop

-- LEFT OFF HERE
--  example (h : ¬¬p → p) : p ∨ ¬p :=  
--    suffices pof : p ∨ false, from or.elim pof (λ h:p, or.inl h) (false.elim),
--    show p ∨ false, from  

end exer

#print "  "
#print "================================================"
#print "Section 3.6 Examples of Propositional Validities"
#print "  "
namespace Section_3_6
variables p q : Prop


end Section_3_6

#print "  "
#print "==============================="
#print "Section 3.7 Exercises"
#print "  "
namespace Section_3_7

end Section_3_7
