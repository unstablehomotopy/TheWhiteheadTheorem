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
import Mathlib.Topology.UnitInterval
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Analysis.InnerProductSpace.PiL2 -- EuclideanSpace
import Mathlib.Init.Set

open CategoryTheory

namespace CWComplex

noncomputable def sphere (n : ℤ) : TopCat :=
  TopCat.of <| Metric.sphere (0 : EuclideanSpace ℝ <| Fin <| Int.toNat <| n + 1) 1

noncomputable def closedBall (n : ℤ) : TopCat :=
  TopCat.of <| Metric.closedBall (0 : EuclideanSpace ℝ <| Fin <| Int.toNat n) 1

notation "𝕊 "n => sphere n
notation "𝔻 "n => closedBall n

def sphereInclusion (n : ℤ) : (𝕊 n) → (𝔻 n + 1) := fun ⟨p, hp⟩ => ⟨p, le_of_eq hp⟩

lemma continuous_sphereInclusion (n : ℤ) : Continuous (sphereInclusion n) :=
  ⟨fun _ ⟨s, _, hs⟩ ↦ by rw [isOpen_induced_iff, ← hs]; tauto⟩

def bundledSphereInclusion (n : ℤ) : TopCat.of (𝕊 n) ⟶ TopCat.of (𝔻 n + 1) :=
  ⟨sphereInclusion n, continuous_sphereInclusion n⟩

def sigmaSphereInclusion (n : ℤ) (cells : Type) :
    (Σ (_ : cells), 𝕊 n) → (Σ (_ : cells), 𝔻 n + 1) :=
  Sigma.map id fun _ x => sphereInclusion n x

lemma continuous_sigmaSphereInclusion (n : ℤ) (cells : Type) :
    Continuous (sigmaSphereInclusion n cells) :=
  Continuous.sigma_map fun _ ↦ continuous_sphereInclusion n

def bundledSigmaSphereInclusion (n : ℤ) (cells : Type) :
    TopCat.of (Σ (_ : cells), 𝕊 n) ⟶ TopCat.of (Σ (_ : cells), 𝔻 n + 1) :=
  ⟨sigmaSphereInclusion n cells, continuous_sigmaSphereInclusion n cells⟩

def sigmaAttachMap (X : TopCat) (n : ℤ) (cells : Type)
    (attach_maps : cells → C(𝕊 n, X)) :
    (Σ (_ : cells), 𝕊 n) → X :=
  fun ⟨i, x⟩ => attach_maps i x

lemma continuous_sigmaAttachMap (X : TopCat) (n : ℤ) (cells : Type)
    (attach_maps : cells → C(𝕊 n, X)) :
    Continuous (sigmaAttachMap X n cells attach_maps) :=
  continuous_sigma fun i => (attach_maps i).continuous_toFun

def bundledSigmaAttachMap (X : TopCat) (n : ℤ) (cells : Type)
    (attach_maps : cells → C(𝕊 n, X)) :
    TopCat.of (Σ (_ : cells), 𝕊 n) ⟶ X :=
  ⟨sigmaAttachMap X n cells attach_maps, continuous_sigmaAttachMap X n cells attach_maps⟩

-- A type witnessing that X' is obtained from X by attaching n-cells
structure AttachCells (X X' : TopCat) (n : ℤ) where
  /- The index type over n-cells -/
  cells : Type
  attach_maps : cells → C(𝕊 n, X)
  iso_pushout : X' ≅ Limits.pushout
    (bundledSigmaSphereInclusion n cells)
    (bundledSigmaAttachMap X n cells attach_maps)

end CWComplex

structure RelativeCWComplex (A : TopCat) where
  /- Skeleta -/
  -- might need this: https://math.stackexchange.com/questions/650279/pushout-from-initial-object-isomorphic-to-coproduct
  sk : ℤ → TopCat
  /- A is isomorphic to the (-1)-skeleton. -/
  iso_sk_neg_one : A ≅ sk (-1)
  /- The (n + 1)-skeleton is obtained from the n-skeleton by attaching (n + 1)-cells. -/
  attach_cells : (n : ℤ) → CWComplex.AttachCells (sk n) (sk (n + 1)) (n + 1)

abbrev CWComplex := RelativeCWComplex (TopCat.of Empty)

namespace CWComplex

noncomputable section Topology

-- The inclusion map from X to X', given that X' is obtained from X by attaching n-cells
def AttachCellsInclusion (X X' : TopCat) (n : ℤ) (att : AttachCells X X' n) : X ⟶ X'
  := @Limits.pushout.inr TopCat _ _ _ X
      (bundledSigmaSphereInclusion n att.cells)
      (bundledSigmaAttachMap X n att.cells att.attach_maps) _ ≫ att.iso_pushout.inv

-- The inclusion map from the n-skeleton to the (n+1)-skeleton of a CW-complex
def skeletaInclusion {A : TopCat} (X : RelativeCWComplex A) (n : ℤ) : X.sk n ⟶ X.sk (n + 1) :=
  AttachCellsInclusion (X.sk n) (X.sk (n + 1)) (n + 1) (X.attach_cells n)

-- The inclusion map from the n-skeleton to the m-skeleton of a CW-complex
def skeletaInclusion' {A : TopCat} (X : RelativeCWComplex A)
    (n : ℤ) (m : ℤ) (n_le_m : n ≤ m) : X.sk n ⟶ X.sk m :=
  if h : n = m then by
    rw [← h]
    exact 𝟙 (X.sk n)
  else by
    have h' : n < m := Int.lt_iff_le_and_ne.mpr ⟨n_le_m, h⟩
    exact skeletaInclusion X n ≫ skeletaInclusion' X (n + 1) m h'
  termination_by Int.toNat (m - n)
  decreasing_by
    simp_wf
    rw [Int.toNat_of_nonneg (Int.sub_nonneg_of_le h')]
    linarith

def ColimitDiagram {A : TopCat} (X : RelativeCWComplex A) : ℤ ⥤ TopCat where
  obj := X.sk
  map := @fun n m n_le_m => skeletaInclusion' X n m <| Quiver.Hom.le n_le_m
  map_id := by simp [skeletaInclusion']
  map_comp := by
    let rec p (n m l : ℤ) (n_le_m : n ≤ m) (m_le_l : m ≤ l) (n_le_l : n ≤ l) :
        skeletaInclusion' X n l n_le_l =
        skeletaInclusion' X n m n_le_m ≫
        skeletaInclusion' X m l m_le_l :=
      if hnm : n = m then by
        unfold skeletaInclusion'
        subst hnm
        simp only [eq_mpr_eq_cast, ↓reduceDite, cast_eq, Category.id_comp]
      else by
        have h1 : n < m := Int.lt_iff_le_and_ne.mpr ⟨n_le_m, hnm⟩
        have h2 : n < l := by linarith
        unfold skeletaInclusion'
        simp [hnm, Int.ne_of_lt h2]
        rcases em (m = l) with hml | hml
        . subst hml
          simp only [↓reduceDite]
          rw [cast_eq, Category.comp_id]
        congr
        rw [p (n + 1) m l h1 m_le_l h2]
        congr
        simp only [hml, ↓reduceDite]
        conv => lhs; unfold skeletaInclusion'
        simp only [hml, ↓reduceDite]
      termination_by Int.toNat (l - n)
      decreasing_by
        simp_wf
        rw [Int.toNat_of_nonneg (Int.sub_nonneg_of_le h2)]
        linarith
    intro n m l n_le_m m_le_l
    have n_le_m := Quiver.Hom.le n_le_m
    have m_le_l := Quiver.Hom.le m_le_l
    exact p n m l n_le_m m_le_l (Int.le_trans n_le_m m_le_l)

-- The topology on a CW-complex.
def toTopCat {A : TopCat} (X : RelativeCWComplex A) : TopCat :=
  Limits.colimit (ColimitDiagram X)

-- TODO: Coe RelativeCWComplex ?
instance : Coe CWComplex TopCat where coe X := toTopCat X

end Topology -- noncomputable section

section GluingLemma

#check ContinuousMap.liftCover -- gluing lemma for an open cover

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

variable {ι : Type*} [Finite ι] (S : ι → Set α) (φ : ∀ i : ι, C(S i, β))
(hφ : ∀ (i j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩)
(hS_cover : ∀ x : α, ∃ i, x ∈ S i) (hS_closed : ∀ i, IsClosed (S i))

noncomputable def liftCoverClosed : C(α, β) :=
  have H : ⋃ i, S i = Set.univ := Set.iUnion_eq_univ_iff.2 hS_cover
  let Φ := Set.liftCover S (fun i ↦ φ i) hφ H
  ContinuousMap.mk Φ <| continuous_iff_isClosed.mpr fun Y hY ↦ by
    have : ∀ i, φ i ⁻¹' Y = S i ∩ Φ ⁻¹' Y := fun i ↦ by
      ext x
      simp
      constructor
      . intro ⟨hxi, hφx⟩
        have : Φ x = φ i ⟨x, hxi⟩ := Set.liftCover_of_mem hxi
        rw [← this] at hφx
        trivial
      . intro ⟨hxi, hφx⟩
        use hxi
        have : Φ x = φ i ⟨x, hxi⟩ := Set.liftCover_of_mem hxi
        rwa [← this]
    have : Φ ⁻¹' Y = ⋃ i, Subtype.val '' (φ i ⁻¹' Y) := by
      conv => rhs; ext x; arg 1; ext i; rw [this]
      conv => rhs; ext x; rw [← Set.iUnion_inter, H]; simp
    rw [this]
    exact isClosed_iUnion_of_finite fun i ↦
      IsClosed.trans (IsClosed.preimage (φ i).continuous hY) (hS_closed i)

theorem liftCoverClosed_coe {i : ι} (x : S i) :
    liftCoverClosed S φ hφ hS_cover hS_closed x = φ i x := by
  rw [liftCoverClosed, ContinuousMap.coe_mk, Set.liftCover_coe _]

theorem liftCoverClosed_coe' {i : ι} (x : α) (hx : x ∈ S i) :
    liftCoverClosed S φ hφ hS_cover hS_closed x = φ i ⟨x, hx⟩ := by
  rw [← liftCoverClosed_coe]

end GluingLemma

section HEP

open unitInterval

def prodMap {W X Y Z : TopCat} (f : W ⟶ X) (g : Y ⟶ Z) : TopCat.of (W × Y) ⟶ TopCat.of (X × Z) :=
  --⟨Prod.map f g, Continuous.prod_map f.continuous_toFun g.continuous_toFun⟩
  f.prodMap g

def prodMkLeft {X Y : TopCat} (y : Y) : X ⟶ TopCat.of (X × Y) :=
  (ContinuousMap.id _).prodMk (ContinuousMap.const _ y)

def inc₀ {X : TopCat} : X ⟶ TopCat.of (X × I) :=
  --⟨fun x => (x, 0), Continuous.Prod.mk_left 0⟩
  --@prodMkLeft X (TopCat.of I) ⟨0, by norm_num, by norm_num⟩
  (ContinuousMap.id _).prodMk (ContinuousMap.const _ 0)

def continuousMapFromEmpty {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (empty : X → Empty) :
  C(X, Y) := {
    toFun := fun x ↦ Empty.rec <| empty x
    continuous_toFun := ⟨fun _ _ ↦ isOpen_iff_nhds.mpr fun x ↦ Empty.rec <| empty x⟩
  }

-- def Jar (n : ℤ) := (𝔻 n + 1) × I

def jarMid (n : ℤ) : Set ((𝔻 n + 1) × I) :=
  {⟨⟨x, _⟩, ⟨y, _⟩⟩ : (𝔻 n + 1) × I | ‖x‖ ≤ 1 - y / 2}

def jarRim (n : ℤ) : Set ((𝔻 n + 1) × I) :=
  {⟨⟨x, _⟩, ⟨y, _⟩⟩ : (𝔻 n + 1) × I | ‖x‖ ≥ 1 - y / 2}

lemma continuous_sub_div_two : Continuous fun (y : ℝ) ↦ 1 - y / 2 :=
  (continuous_sub_left _).comp <| continuous_mul_right _

lemma isClosed_jarMid (n : ℤ) : IsClosed (jarMid n) :=
  continuous_iff_isClosed.mp (continuous_subtype_val.norm.prod_map continuous_id)
    {⟨x, y, _⟩ : ℝ × I | x ≤ 1 - y / 2} <| isClosed_le continuous_fst <|
    continuous_sub_div_two.comp <| continuous_subtype_val.comp continuous_snd

lemma isClosed_jarRim (n : ℤ) : IsClosed (jarRim n) :=
  continuous_iff_isClosed.mp (continuous_subtype_val.norm.prod_map continuous_id)
    {⟨x, y, _⟩ : ℝ × I | x ≥ 1 - y / 2} <| isClosed_le
    (continuous_sub_div_two.comp <| continuous_subtype_val.comp continuous_snd) continuous_fst

end HEP
