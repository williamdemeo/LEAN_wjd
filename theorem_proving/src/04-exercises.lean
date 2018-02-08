namespace Sec_4_6

  namespace exercise1
    variables (α : Type) (p q : α → Prop)
    example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := iff.intro
      (assume h : ∀ x, p x ∧ q x,
        and.intro 
        (assume w,
          show p w, from (h w).left)
        (assume w,
          show q w, from (h w).right))
      (assume h : (∀ x, p x) ∧ (∀ x, q x),
        assume w,
        ⟨(h.left w), (h.right w)⟩)


    example : (∀ x, (p x → q x)) → (∀ x, p x) → (∀ x, q x) := 
      assume h₁ : ∀ x, (p x → q x),
      assume h₂ : (∀ x, p x),
      assume w,
      have h₃ : p w, from h₂ w,
      show q w, from h₁ w h₃

    example : (∀ x, p x) ∨ (∀ x, q x) → (∀ x, p x ∨ q x) := 
      assume h: (∀ x, p x) ∨ (∀ x, q x),
      assume w,
        or.elim h
          (assume hl : ∀ x, p x,
            show p w ∨ q w, from or.intro_left _ (hl w))
          (assume hr : ∀ x, q x,
            show p w ∨ q w, from or.intro_right _ (hr w))
  
  end exercise1


    
end Sec_4_6
