import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.Topology.Order
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Analysis.InnerProductSpace.PiL2 -- EuclideanSpace
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
-- This is proved by rfl for any specific natural number n (e.g., n = 100).
theorem map_id_100 (f : PrefunctorFromNat C) :
    (n_add_n_sub_n f 100) ▸ (RangeCompose f 100 (100 - 100)) = 𝟙 (f.obj 100) := rfl

-- But I'm stuck on the general case. Any help is appreciated!
theorem map_id (f : PrefunctorFromNat C) :
    (n : ℕ) -> (n_add_n_sub_n f n) ▸ (RangeCompose f n (n - n)) = 𝟙 (f.obj n) := by
  intro n
  sorry

----------------------------------------------------------

#check TopCat.sigmaIsoSigma
#check EuclideanSpace ℝ (Fin 3)
#check Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
#check Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1 -- open ball
#check TopologicalSpace (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)

/- sphere in ℝⁿ with radius 1 -/
notation:0 "𝕊" n => Metric.sphere (0 : EuclideanSpace ℝ <| Fin <| n + 1) 1
/- open ball in ℝⁿ with radius 1 -/
notation:0 "𝔹" n => Metric.ball (0 : EuclideanSpace ℝ <| Fin n) 1
/- closed ball (disc) in ℝⁿ with radius 1 -/
notation:0 "𝔻" n => Metric.closedBall (0 : EuclideanSpace ℝ <| Fin n) 1

set_option trace.Meta.synthInstance true in
#check TopologicalSpace (Metric.sphere (0 : EuclideanSpace ℝ <| Fin <| 0) 1) -- S (-1) is empty
#check TopologicalSpace (𝕊 0)
#check TopologicalSpace (𝕊 1)
#check TopologicalSpace <| Set.Elem (𝕊 1)
#check TopologicalSpace (𝔻 2)
#check TopCat.of (𝕊 1)
#check TopCat.sigmaIsoSigma
#check TopCat

namespace tmp_namespace_1
  variable (X : Type) [TopologicalSpace X]
  set_option trace.Meta.synthInstance true in
  #check TopologicalSpace { x : X | true } -- subset
  --#check TopologicalSpace { x : X // true } -- subtype

  universe u v w
  def sigmaIsoSigma₁ {ι : Type u} (α : ι → TopCatMax.{u, v}) : ∐ α ≅ TopCat.of (Σi, α i) := sorry
  #check sigmaIsoSigma₁
  #check (cells : Type u) → (α : cells → TopCatMax.{u, v}) → ∐ α ≅ TopCat.of (Σi, α i)
  -- #check (cells : Type v) → (α : cells → TopCatMax.{u, v}) → ∐ α ≅ TopCat.of (Σi, α i) -- fail
  def sigmaIsoSigma₂ {ι : Type*} (α : ι → TopCat) : TopCat.of (Σi, α i) := sorry
  #check sigmaIsoSigma₂
  def sigmaIsoSigma₃ {ι : Type*} (α : ι → TopCat) : (∐ α : TopCat) := sorry
  #check sigmaIsoSigma₃
  def sigmaIsoSigma₄ {ι : Type*} (α : ι → TopCat) : ∐ α ≅ TopCat.of (Σi, α i) := sorry
  #check sigmaIsoSigma₄

  --set_option trace.Meta.synthInstance true in
  --#check {cells : Type*} → (α : cells → TopCat) → (∀ i, α i = TopCat.of (𝕊 1)) → (∐ α : TopCat) --???
  #check {cells : Type*} → TopCat.of (Σ (_ : cells), 𝕊 1)

  variable (cells : Type)
  noncomputable def S1 := TopCat.of (𝕊 1) -- noncomputable because of ENNReal.instCanonicallyOrderedCommSemiringENNReal
  noncomputable def sumS := TopCat.of (Σ (_ : cells), 𝕊 1)
  noncomputable def sumD := TopCat.of (Σ (_ : cells), 𝔻 2)
end tmp_namespace_1

namespace tmp_namespace_2
noncomputable section
  def S1_to_D2_₁ : (𝕊 1) → (𝔻 2) := by
    intro ⟨pt, hpt⟩ -- pt is in ℝ 2; hpt says the distance from x to 0 is 1
    simp [Metric.sphere] at hpt
    have x : ℝ := pt 0 -- x coordinate of the point
    have y : ℝ := pt 1
    use pt
    simp [Metric.closedBall]
    exact le_of_eq hpt
  def S1_to_D2 : (𝕊 1) → (𝔻 2) := fun ⟨pt, hpt⟩ => ⟨pt, le_of_eq hpt⟩
  theorem continuous_S1_to_D2 : Continuous S1_to_D2 := ⟨by
    intro s hs
    rw [isOpen_induced_iff] at *
    obtain ⟨t, ht, ht'⟩ := hs
    use t, ht
    rw [ht'.symm]
    -- note: the two occurences of "Subtype.val" are not of the same type, so we can't apply Eq.trans ht'
    ext ⟨xval, xprop⟩
    repeat
      rw [Set.mem_preimage]
    constructor
    repeat
      intro h
      dsimp [S1_to_D2] at *
      exact h
  ⟩

  variable (cells : Type)
  def sumS1 := TopCat.of (Σ (_ : cells), 𝕊 1)
  def sumD2 := TopCat.of (Σ (_ : cells), 𝔻 2)
  def sumS1' := (Σ (_ : cells), 𝕊 1)
  def sumD2' := (Σ (_ : cells), 𝔻 2)
  -- def sumS1_to_sumD2 :
  --   TopCat.of (Σ (_ : cells), 𝕊 1) → TopCat.of (Σ (_ : cells), 𝔻 2) :=
  --   fun ⟨i, x⟩ => ⟨i, S1_to_D2 x⟩
  -- def sumS1_to_sumD2' :
  --   (Σ (_ : cells), 𝕊 1) → (Σ (_ : cells), 𝔻 2) :=
  --   fun ⟨i, x⟩ => ⟨i, S1_to_D2 x⟩
  -- #check sumS1_to_sumD2
  -- #check sumS1_to_sumD2'
  -- theorem continuous_sumS1_to_sumD2 : Continuous <| sumS1_to_sumD2 cells := by
  --   apply continuous_sigma
  --   intro i
  --   dsimp [sumS1_to_sumD2]
  --   sorry
  def sumS1_to_sumD2:
    TopCat.of (Σ (_ : cells), 𝕊 1) → TopCat.of (Σ (_ : cells), 𝔻 2) :=
    Sigma.map id fun (_ : cells) (x : 𝕊 1) => S1_to_D2 x
  theorem continuous_sumS1_to_sumD2 : Continuous <| sumS1_to_sumD2 cells := by
    apply Continuous.sigma_map
    intro _
    apply continuous_S1_to_D2
  #check continuous_sigmaMk
  #check continuous_sigma_map
  #check Continuous.sigma_map
  #check continuous_inclusion
  --theorem continuous_sumS1_to_sumD2 : Continuous sumS1_to_sumD2 := by

  #check @CategoryTheory.Limits.pushout TopCat _
  #check CategoryTheory.Limits.HasPushout
end

section
  #check CategoryTheory.Limits.colimit

  --set_option trace.Meta.synthInstance true
  #check (Functor ℕ ℕ)
  #check (Preorder.smallCategory ℕ)

  #check Eq.mpr
  #check CategoryTheory.eqToHom
  #check cast

  #eval [1, 2, 3, 4, 5].foldl (·*·) 1
  #eval [1, 2, 3, 4, 5].foldr (·*·) 1
  #check List.range'
  #check List.foldl_assoc
end
end tmp_namespace_2

----------------------------------------------------------
