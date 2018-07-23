/-
Copyright (c) 2015 William DeMeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: William DeMeo <williamdemeo@gmail.com>

Notes, examples, solutions from Logic and Proof book.
-/

import data.set
open set

variable {U : Type}
variables A B C : set U
variables x : U

#check x ∈ A
#check A ∪ B
#check B \ C
#check A ∩ C
#check -C
#check ∅ ⊆ A
#check ∅ ⊂ A
#check B ⊆ univ
#reduce ∅ ⊆ A


example (A B : set U) : A ⊆ A ∪ B := assume x, assume h: x ∈ A, 
  show x ∈ A ∪ B, from or.inl h
example (A B : set U) : A ⊆ A ∪ B := assume x, assume : x ∈ A, 
  show x ∈ A ∪ B, from or.inl ‹ x ∈ A › 
example (A B : set U) : A ⊆ A ∪ B := assume x, assume : x ∈ A, 
  show x ∈ A ∪ B, from mem_union_left B ‹ x ∈ A › 

--
example : ∀ x, x ∈ A → x ∈ B → x ∈ A ∩ B := assume x, assume : x ∈ A, 
  assume : x ∈ B, show x ∈ A ∩ B, from and.intro ‹ x ∈ A › ‹ x ∈ B › 
example : ∀ x, x ∈ A → x ∈ B → x ∈ A ∩ B := assume x, assume h₁ : x ∈ A, 
  assume h₂ : x ∈ B, show x ∈ A ∩ B, from and.intro h₁ h₂ 
example : ∀ x, x ∈ A → x ∈ B → x ∈ A ∩ B := assume x, assume : x ∈ A, 
  assume : x ∈ B, show x ∈ A ∩ B, from mem_inter ‹ x ∈ A › ‹ x ∈ B › 
--
example : ∅ ⊆ A := assume x, assume : x ∈ ∅,
  show x ∈ A, from false.elim ‹ x ∈ (∅ : set U) ›   
example : ∅ ⊆ A := assume x, assume h : x ∈ (∅ : set U), 
  show x ∈ A, from false.elim h
example : ∅ ⊆ A := assume x, assume : x ∈ ∅,
  show x ∈ A, from absurd ‹ x ∈ ∅ › 
  (not_mem_empty x) -- this line means x ∉ ∅ 

#reduce A \ B  -- λ (a : U), A a ∧ (B a → false)

example : A \ B ⊆ A :=
assume x,
assume h : x ∈ A \ B,
show x ∈ A, from and.left h

#check @mem_inter
#check @mem_of_mem_inter_left 
#check @mem_of_mem_inter_right
#check @mem_union_left
#check @mem_union_right
#check @mem_or_mem_of_mem_union
#check @not_mem_empty



  
