import Mathlib.CategoryTheory.Category.Basic
open CategoryTheory

universe u v
variable {C : Type u} [Category.{v} C]

structure PrefunctorFromNat (C : Type u) [Category.{v} C] where
  obj : (n : ℕ) -> C
  hom : (n : ℕ) -> (obj n) ⟶ (obj <| n + 1)

def RangeCompose (f : PrefunctorFromNat C) : (start len : ℕ) → (f.obj start ⟶ f.obj <| start + len)
  | s, 0     => 𝟙 (f.obj s)
  | s, l + 1 => by
    rw [<- Nat.succ_add_eq_add_succ s l]
    exact f.hom s ≫ RangeCompose f (s + 1) l

-- -- Now I can define a functor from the prefunctor like this:
-- def RangeCompose' (f : PrefunctorFromNat C) (n m : ℕ) (n_le_m : n ≤ m) : (f.obj n ⟶ f.obj m) := by
--   rw [<- Nat.add_sub_of_le n_le_m]
--   exact RangeCompose f n (m - n)

lemma n_add_n_sub_n (f : PrefunctorFromNat C) (n : ℕ) :
    (f.obj n ⟶ f.obj (n + (n - n))) = (f.obj n ⟶ f.obj n) :=
  by rw [Nat.add_sub_of_le Nat.le.refl]

-- I'd like to show that the prefunctor preserves identity morphisms.
-- This is proved by rfl for any specific natural number n (e.g., n = 100), but...
theorem map_id_100 (f : PrefunctorFromNat C) :
    (n_add_n_sub_n f 100) ▸ (RangeCompose f 100 (100 - 100)) = 𝟙 (f.obj 100) := rfl

-- I'm stuck on the general case. Any help is appreciated!
theorem map_id (f : PrefunctorFromNat C) :
    (n : ℕ) -> (n_add_n_sub_n f n) ▸ (RangeCompose f n (n - n)) = 𝟙 (f.obj n) := by
  intro n
  sorry
