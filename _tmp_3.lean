-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Help.3A.20tactic.20'rewrite'.20failed.2C.20motive.20is.20not.20type.20correct
-- https://leanprover-community.github.io/mathlib4_docs/docs/Conv/Guide.html
-- https://leanprover-community.github.io/mathlib4_docs/docs/Conv/Introduction.html

import Mathlib.Tactic
import Mathlib.Data.List.Basic


structure Vector' (n : Nat) where
  data : List Nat
  lenc : (List.length data = n)

def append (a : Vector' n) (b : Vector' m) : Vector' (n + m) :=
  ⟨a.data ++ b.data, by simp only [List.length_append, a.lenc, b.lenc]⟩

theorem zero_append (h : 0 + n = n) (a : Vector' n) :
  h ▸ (append ⟨[], by decide⟩ a) = a := by
  simp [append]
  revert h
  rw [zero_add] -- tactic 'rewrite' failed, motive is not type correct
  sorry


-- type cast proof
-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Type.20cast.20proof

example {X : Type} {n : Nat} {l : List X} {l_len : n = l.length} {x : X}
  {h : ∃ j, l.get j = x} : ∃ (j : Fin n), l.get (l_len ▸ j) = x := by
  subst l_len
  simp [h]

example {n : Nat} {l : List (Fin n)} {l_len : n = l.length} {x : Fin n}
    {h : ∃ j, l.get j = x} : ∃ (j : Fin n), l.get (l_len ▸ j) = x := by
  -- obtain ⟨⟨j, h'⟩, r⟩ := h
  -- rw [<- r]
  obtain ⟨⟨j, h'⟩, rfl⟩ := h
  use! j
  · convert h'
  · congr
    generalize Fin n = X at l
    subst l_len
    rfl
