### Three proofs of append_nil

```lean
  theorem nil_append (t : my_list α) : nil ++ t = t := rfl
  theorem cons_append (x : α) (s t : my_list α) : (x :: s) ++ t = x :: (s ++ t) := rfl
```
---

```lean
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

```
---

```lean
  -- Second try:
  theorem append_nil₂ (t : my_list α) : t ++ nil = t := my_list.rec_on t 
    (show (append nil nil) = nil, from rfl)
  (assume (x : α), assume (t : my_list α),
   assume ih : (append t nil) = t,
     calc
       append (x :: t) nil = x :: append t nil  : cons_append x t nil
                       ... = x :: t             : by rw ih)
```
---

```lean
  -- Third try:
  theorem append_nil₃ (t : my_list α) : t ++ nil = t := my_list.rec_on t 
    rfl  -- (base)
    (λ (x : α) (t : my_list α) (ih : (append t nil) = t), by simp [cons_append, ih]) -- (induct)
```
