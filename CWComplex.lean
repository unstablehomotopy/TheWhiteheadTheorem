/-
The definition of CW complexes follows David Wärn's suggestion at
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Do.20we.20have.20CW.20complexes.3F/near/231769080
-/

import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.Topology.Order
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.Analysis.InnerProductSpace.PiL2 -- EuclideanSpace

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
end
end tmp_namespace_2

#check CategoryTheory.Limits.pushout


----------------------------------------------------------

noncomputable section

--universe u v w x
--variable {F : Type*} {X : Type u} {X' : Type v} {Y : Type w} {Z : Type x} {ι : Type*}
--variable [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y]

def CellBorderInclusion (n : ℕ) : (𝕊 n) → (𝔻 n + 1) := fun ⟨pt, hpt⟩ => ⟨pt, le_of_eq hpt⟩

theorem continuous_cellBorderInclusion (n : ℕ) : Continuous (CellBorderInclusion n) :=
  ⟨by
    intro s hs
    rw [isOpen_induced_iff] at *
    obtain ⟨t, ht, ht'⟩ := hs
    use t, ht
    rw [ht'.symm]
    ext ⟨xval, xprop⟩
    repeat
      rw [Set.mem_preimage]
    constructor
    repeat
      intro h
      dsimp [CellBorderInclusion] at *
      exact h
  ⟩

def SigmaCellBorderInclusion (n : ℕ) (cells : Type) :
  TopCat.of (Σ (_ : cells), 𝕊 n) → TopCat.of (Σ (_ : cells), 𝔻 n + 1) :=
    Sigma.map id fun _ x => CellBorderInclusion n x

theorem continuous_sigmaCellBorderInclusion (n : ℕ) (cells : Type) :
  Continuous (SigmaCellBorderInclusion n cells) := by
    apply Continuous.sigma_map
    intro _
    apply continuous_cellBorderInclusion

def BundledSigmaCellBorderInclusion (n : ℕ) (cells : Type) :
  ContinuousMap (TopCat.of (Σ (_ : cells), 𝕊 n)) (TopCat.of (Σ (_ : cells), 𝔻 n + 1)) :=
    ⟨SigmaCellBorderInclusion n cells, continuous_sigmaCellBorderInclusion n cells⟩

def SigmaAttachMap (X : Type) [TopologicalSpace X]
  (n : ℕ) (cells : Type) (attach_maps : cells → ContinuousMap (TopCat.of (𝕊 n)) (TopCat.of X)) :
  TopCat.of (Σ (_ : cells), 𝕊 n) → TopCat.of X :=
    fun ⟨i, x⟩ => attach_maps i x

theorem continuous_sigmaAttachMap (X : Type) [TopologicalSpace X]
  (n : ℕ) (cells : Type) (attach_maps : cells → ContinuousMap (TopCat.of (𝕊 n)) (TopCat.of X)) :
  Continuous (SigmaAttachMap X n cells attach_maps) := by
    apply continuous_sigma
    exact fun i => ContinuousMap.continuous (attach_maps i)

def BundledSigmaAttachMap (X : Type) [TopologicalSpace X]
  (n : ℕ) (cells : Type) (attach_maps : cells → ContinuousMap (TopCat.of (𝕊 n)) (TopCat.of X)) :
  ContinuousMap (TopCat.of (Σ (_ : cells), 𝕊 n)) (TopCat.of X) :=
    ⟨SigmaAttachMap X n cells attach_maps, continuous_sigmaAttachMap X n cells attach_maps⟩

-- A type witnessing that X' is obtained from X by attaching n-cells
structure AttachCells (X X' : Type) [TopologicalSpace X] [TopologicalSpace X'] (n : ℕ) where
  /- The index type over n-cells -/
  cells : Type
  attach_maps : cells → ContinuousMap (TopCat.of (𝕊 n)) (TopCat.of X)
  --attach_maps : cells → ContinuousMap (𝕊 n) X
  iso_pushout : (TopCat.of X') ≅ CategoryTheory.Limits.pushout
    (BundledSigmaCellBorderInclusion n cells)
    (BundledSigmaAttachMap X n cells attach_maps)
  -- pushout : (TopCat.of X') ≅ @CategoryTheory.Limits.pushout TopCat _
  --   (TopCat.of (Σ (_ : cells), 𝕊 n))
  --   (TopCat.of (Σ (_ : cells), 𝔻 n + 1))
  --   (TopCat.of X)
  --   (BundledSigmaCellBorderInclusion n cells)
  --   (BundledSigmaAttachMap X n cells attach_maps continuous_attach_maps) _

-- structure CWComplex where
--   /- Skeleta -/
--   sk : ℤ → TopCat
--   /- Every n-skeleton for n < 0 is empty. -/
--   sk_neg_empty : ∀ n < 0, sk n = Empty
--   /- For n ≥ 0, the (n-1)-skeleton is obtained from the n-skeleton by attaching n-cells. -/
--   attach_cells : (n : ℕ) → AttachCells (sk (n - 1)) (sk n) n

-- -- A type witnessing that X' is obtained from X by attaching n-cells
-- structure AttachCells (X X' : Type*) [TopologicalSpace X] [TopologicalSpace X'] (n : ℕ) where
--   inclusion : C(X, X')
--   cells : Type
-- -- should also have, for each i in cells a map ∂D n ⟶ X, and
-- -- a homeomorphism between X' and the result of gluing these n-cells to X

structure CWComplex where
  /- Skeleta -/
  sk : ℕ → TopCat
  /- The 0-skeleton is a discrete topological space. -/
  discrete_sk_zero : DiscreteTopology (sk 0)
  /- The (n+1)-skeleton is obtained from the n-skeleton by attaching (n+1)-cells. -/
  attach_cells : (n : ℕ) → AttachCells (sk n) (sk (n + 1)) (n + 1)

end
