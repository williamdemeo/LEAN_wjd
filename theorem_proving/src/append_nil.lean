print "==========================================="
#print "Section 7.5. Other Recursive Data Types"
#print " "
-- https://leanprover.github.io/theorem_proving_in_lean/inductive_types.html#other-recursive-data-types

-- Here are some more examples of inductively defined types.
namespace Sec_7_5
  -- For any type, α, the type list α of lists of elements of α is defined in the library.
  universe u
  inductive my_list (α : Type u)
  | nil {} : my_list
  | cons : α → my_list → my_list

  namespace my_list
  
  variable {α : Type}
  
  notation h :: t := cons h t

  def append (s t : my_list α) : my_list α := 
  (my_list.rec t (λ (x: α) (l: my_list α) (v: my_list α), x :: v)) s
  /- Dissection of append: 
     The first arg to `list.rec` is `t`, meaning return `t` when `s` is `null`.
     The second arg is `(λ x l v, x :: v) s`.  I *think* this means the following:
     assuming `v` is the result of `append l t`, then `append (x :: l) t` results
     in `x :: v`.  

     ==========> UNRESOLVED QUESTION:  What about `s` ....?   <==========
  -/

  /- To give some support for the claim that the foregoing interpretation is (roughtly) 
     correct, let's make the types explicit and verify that the definition still type-checks: -/
  def append' (s t : my_list α) : my_list α := 
  my_list.rec (t: my_list α) (λ (x : α) (l : my_list α) (u: my_list α), x :: u) (s : my_list α)

  #check nil                       -- nil : list ?M_1
  #check (nil : my_list ℕ)           -- nil : list ℕ
  #check cons 0 nil                -- 0 :: nil : list ℕ
  #check cons "a" nil              -- 0 :: nil : list string
  #check cons "a" (cons "b" nil)   -- a :: b :: nil : list string

  notation s ++ t := append s t

  theorem nil_append (t : my_list α) : nil ++ t = t := rfl

  theorem cons_append (x : α) (s t : my_list α) : (x :: s) ++ t = x :: (s ++ t) := rfl

  
  -- Lean allows us to define iterative notation for lists:

  notation `{` l:(foldr `,` (h t, cons h t) nil) `}` := l

  section
    open nat
    #check {1,2,3,4,5}               -- Lean assumes this is a list of nats
    #check ({1,2,3,4,5} : my_list int)  -- Forces Lean to take this as a list of ints.
  end 


  -- As an exercise, prove the following:
  -- `theorem append_nil (t : my_list α) : t ++ nil = t

  -- First try:
  theorem append_nil₁ (t : my_list α) : t ++ nil = t := my_list.rec_on t 
    (show (append nil nil) = nil, from rfl)
    (assume (x : α), assume (t : my_list α),
    assume ih : (append t nil) = t,
    show append (x :: t) nil = (x :: t), from
      have h1: append (x :: t) nil = x :: (append t nil), from cons_append x t nil,
      have h2: x :: (append t nil) = x :: t, from congr_arg _ ih,
      eq.trans h1 h2
    )
  -- Second try:
  theorem append_nil₂ (t : my_list α) : t ++ nil = t := my_list.rec_on t 
    (show (append nil nil) = nil, from rfl)
  (assume (x : α), assume (t : my_list α),
   assume ih : (append t nil) = t,
     calc
       append (x :: t) nil = x :: append t nil  : cons_append x t nil
                       ... = x :: t             : by rw ih)
  -- Third try:
  theorem append_nil₃ (t : my_list α) : t ++ nil = t := my_list.rec_on t 
    rfl  -- (base)
    (λ (x : α) (t : my_list α) (ih : (append t nil) = t), by simp [cons_append, ih]) -- (induct)

  -- binary trees
  inductive binary_tree
  | leaf : binary_tree
  | node : binary_tree → binary_tree → binary_tree

  -- countably branching trees
  inductive cbtree
  | leaf : cbtree
  | sup : (ℕ → cbtree) → cbtree

  namespace cbtree
  
  def succ (t : cbtree) : cbtree := sup (λ n, t)  -- Note: (λ n, t) is a thunk; i.e., a way to
                                                  -- view t as a function of type ℕ → cbtree.

  /- Note the similarity to nat's successor.  The third cbtree after t would be 
     `sup (λ n, sup (λ n, sup (λ n, t))` -/

  def omega : cbtree := sup (λ n, nat.rec_on n leaf (λ n t, succ t))
  end cbtree
  end my_list
           
end Sec_7_5

