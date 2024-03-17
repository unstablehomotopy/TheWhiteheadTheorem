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
--import Mathlib.Data.Finset.Basic

open CategoryTheory


namespace CWComplex
noncomputable section

def Sphere : ℤ → TopCat
  | (n : ℕ) => TopCat.of <| Metric.sphere (0 : EuclideanSpace ℝ <| Fin <| n + 1) 1
  | _       => TopCat.of Empty

def ClosedBall : ℤ → TopCat
  | (n : ℕ) => TopCat.of <| Metric.closedBall (0 : EuclideanSpace ℝ <| Fin n) 1
  | _       => TopCat.of Empty

notation:0 "𝕊 "n => Sphere n
notation:0 "𝔻 "n => ClosedBall n

def SphereInclusion (n : ℤ) : (𝕊 n) → (𝔻 n + 1) :=
  match n with
  | Int.ofNat _   => fun ⟨pt, hpt⟩ => ⟨pt, le_of_eq hpt⟩
  | Int.negSucc _ => Empty.rec

theorem continuous_sphereInclusion (n : ℤ) : Continuous (SphereInclusion n) :=
  match n with
  | Int.ofNat _ => ⟨by
      intro _ ⟨t, ht, ht'⟩
      rw [isOpen_induced_iff]
      use t, ht
      rw [ht'.symm]
      tauto⟩
  | Int.negSucc n => ⟨by tauto⟩

def BundledSphereInclusion (n : ℤ) : TopCat.of (𝕊 n) ⟶ TopCat.of (𝔻 n + 1) :=
  ⟨SphereInclusion n, continuous_sphereInclusion n⟩

def SigmaSphereInclusion (n : ℤ) (cells : Type) :
    (Σ (_ : cells), 𝕊 n) → (Σ (_ : cells), 𝔻 n + 1) :=
  Sigma.map id fun _ x => SphereInclusion n x

theorem continuous_sigmaSphereInclusion (n : ℤ) (cells : Type) :
    Continuous (SigmaSphereInclusion n cells) := by
  apply Continuous.sigma_map
  intro _
  apply continuous_sphereInclusion

def BundledSigmaSphereInclusion (n : ℤ) (cells : Type) :
    TopCat.of (Σ (_ : cells), 𝕊 n) ⟶ TopCat.of (Σ (_ : cells), 𝔻 n + 1) :=
  ⟨SigmaSphereInclusion n cells, continuous_sigmaSphereInclusion n cells⟩

def SigmaAttachMap (X : TopCat) (n : ℤ) (cells : Type)
    (attach_maps : cells → C(𝕊 n, X)) :
    (Σ (_ : cells), 𝕊 n) → X :=
  fun ⟨i, x⟩ => attach_maps i x

theorem continuous_sigmaAttachMap (X : TopCat) (n : ℤ) (cells : Type)
    (attach_maps : cells → C(𝕊 n, X)) :
    Continuous (SigmaAttachMap X n cells attach_maps) := by
  apply continuous_sigma
  exact fun i => (attach_maps i).continuous_toFun

def BundledSigmaAttachMap (X : TopCat) (n : ℤ) (cells : Type)
    (attach_maps : cells → C(𝕊 n, X)) :
    TopCat.of (Σ (_ : cells), 𝕊 n) ⟶ X :=
  ⟨SigmaAttachMap X n cells attach_maps, continuous_sigmaAttachMap X n cells attach_maps⟩

-- A type witnessing that X' is obtained from X by attaching n-cells
structure AttachCells (X X' : TopCat) (n : ℤ) where
  /- The index type over n-cells -/
  cells : Type
  attach_maps : cells → C(𝕊 n, X)
  iso_pushout : X' ≅ Limits.pushout
    (BundledSigmaSphereInclusion n cells)
    (BundledSigmaAttachMap X n cells attach_maps)

end
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
noncomputable section

-- The inclusion map from X to X', given that X' is obtained from X by attaching n-cells
def AttachCellsInclusion (X X' : TopCat) (n : ℤ) (att : AttachCells X X' n) : X ⟶ X'
  := @Limits.pushout.inr TopCat _ _ _ X
      (BundledSigmaSphereInclusion n att.cells)
      (BundledSigmaAttachMap X n att.cells att.attach_maps) _ ≫ att.iso_pushout.inv

-- The inclusion map from the n-skeleton to the (n+1)-skeleton of a CW-complex
def SkeletaInclusion {A : TopCat} (X : RelativeCWComplex A) (n : ℤ) : X.sk n ⟶ X.sk (n + 1) :=
  AttachCellsInclusion (X.sk n) (X.sk (n + 1)) (n + 1) (X.attach_cells n)

-- The inclusion map from the n-skeleton to the m-skeleton of a CW-complex
def SkeletaInclusion' {A : TopCat} (X : RelativeCWComplex A)
    (n : ℤ) (m : ℤ) (n_le_m : n ≤ m) : X.sk n ⟶ X.sk m :=
  if h : n = m then by
    rw [<- h]
    exact 𝟙 (X.sk n)
  else by
    have h' : n < m := Int.lt_iff_le_and_ne.mpr ⟨n_le_m, h⟩
    exact SkeletaInclusion X n ≫ SkeletaInclusion' X (n + 1) m h'
  termination_by Int.toNat (m - n)
  decreasing_by
    simp_wf
    rw [Int.toNat_of_nonneg (Int.sub_nonneg_of_le h')]
    linarith

def ColimitDiagram {A : TopCat} (X : RelativeCWComplex A) : ℤ ⥤ TopCat where
  obj := X.sk
  map := @fun n m n_le_m => SkeletaInclusion' X n m <| Quiver.Hom.le n_le_m
  map_id := by simp [SkeletaInclusion']
  map_comp := by
    let rec p (n m l : ℤ) (n_le_m : n ≤ m) (m_le_l : m ≤ l) (n_le_l : n ≤ l) :
        SkeletaInclusion' X n l n_le_l =
        SkeletaInclusion' X n m n_le_m ≫
        SkeletaInclusion' X m l m_le_l :=
      if hnm : n = m then by
        unfold SkeletaInclusion'
        aesop
      else by
        have h1 : n < m := Int.lt_iff_le_and_ne.mpr ⟨n_le_m, hnm⟩
        have h2 : n < l := by linarith
        unfold SkeletaInclusion'
        simp [hnm, Int.ne_of_lt h2]
        rcases em (m = l) with hml | hml
        . aesop
        congr
        rw [p (n + 1) m l h1 m_le_l h2]
        congr
        simp [hml]
        conv => lhs; unfold SkeletaInclusion'
        simp [hml]
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

instance : Coe CWComplex TopCat where coe X := toTopCat X


open unitInterval

-- def j0 {X : TopCat} : X ⟶ TopCat.of (X × I) := ⟨fun x => (x, 0), Continuous.Prod.mk_left 0⟩
-- def prod_map {W X Y Z : TopCat} (f : W ⟶ X) (g : Y ⟶ Z) : TopCat.of (W × Y) ⟶ TopCat.of (X × Z) :=
--   ⟨Prod.map f g, Continuous.prod_map f.continuous_toFun g.continuous_toFun⟩
-- def HomotopyExtensionProperty {A X : TopCat} (i : A ⟶ X) : Prop :=
--   ∀ Y : TopCat, ∀ f : X ⟶ Y, ∀ H : TopCat.of (A × I) ⟶ Y, i ≫ f = j0 ≫ H →
--   ∃ H' : TopCat.of (X × I) ⟶ Y, f = j0 ≫ H' ∧ H = prod_map i (𝟙 (TopCat.of I)) ≫ H'

-- def j0 {X : Type} [TopologicalSpace X] : C(X, X × I) := ⟨fun x => (x, 0), Continuous.Prod.mk_left 0⟩

def HomotopyExtensionProperty {A X : Type} [TopologicalSpace A] [TopologicalSpace X] (i : C(A, X)) : Prop :=
  ∀ Y : Type, [TopologicalSpace Y] → ∀ f : C(X, Y), ∀ H : C(A × I, Y), f ∘ i = H ∘ (., 0) →
  ∃ H' : C(X × I, Y), f = H' ∘ (., 0) ∧ H = H' ∘ Prod.map i id

theorem hep_sphereInclusion (n : ℤ) : HomotopyExtensionProperty (BundledSphereInclusion n) :=
--theorem hep_sphereInclusion (n : ℤ) : HomotopyExtensionProperty ⟨SphereInclusion n, continuous_sphereInclusion n⟩ :=
  match n with
  | (n : ℕ) => sorry
  | Int.negSucc n' => -- n = -(n' + 1)
    if h_neg_one : n' = 0 then by
      rw [h_neg_one]
      intro Y _ f H hcomp
      use ⟨fun (x, _) => f x, Continuous.fst' f.continuous_toFun⟩ -- f ∘ Prod.fst
      simp
      constructor
      . ext x
        simp
      ext ⟨x, _⟩
      tauto -- Empty.rec x
    else by
      have h_neg_one : n' > 0 := Nat.pos_of_ne_zero h_neg_one
      have h_neg_one₁ : Int.negSucc n' < 0 := Int.negSucc_lt_zero n'
      have h_neg_one₂ : Int.negSucc n' < 0 := Int.negSucc_lt_zero n'
      have h_neg_one' : Int.negSucc n' + 1 < 0 := by
        sorry
      intro Y _ f H hcomp
      -- have H' : Empty → Y := Empty.rec
      -- have H' : (𝔻 (Int.negSucc n)) → Y := Empty.rec
      let H' : (𝔻 Int.negSucc n') × I → Y := fun (x, _) => Empty.rec x
      let H' : (𝔻 Int.negSucc n' + 1) × I → Y := by
        intro (x, _)
        unfold ClosedBall at x
        sorry
      sorry

theorem hep_sphereInclusion' (n : ℤ) : HomotopyExtensionProperty ⟨SphereInclusion n, continuous_sphereInclusion n⟩ :=
  if h1 : n = -1 then by
    rw [h1]
    intro Y _ f H hcomp
    use ⟨fun (x, _) => f x, Continuous.fst' f.continuous_toFun⟩ -- f ∘ Prod.fst
    simp
    constructor
    . ext x
      simp
    ext ⟨x, _⟩
    tauto
  else if h2 : n + 1 < 0 then by
    have ⟨m, hm⟩ := Int.eq_negSucc_of_lt_zero h2
    intro Y _ f H hcomp
    --rw [hm] at f
    let φ (n : ℕ) : C(𝔻 Int.negSucc n, Y) := ⟨Empty.rec, by tauto⟩
    let φ' (n : ℕ) : C((𝔻 Int.negSucc n) × I, Y) :=
      ⟨fun (x, _) => φ n x, Continuous.fst' (φ n).continuous_toFun⟩
    let H' : C((𝔻 n + 1) × I, Y) := by rw [hm]; exact φ' m
    use H'
    constructor
    . ext x
      dsimp
      sorry
    ext ⟨x, z⟩
    simp
    sorry
  else by
    have h3 : n ≥ 0 := by contrapose! h2; contrapose! h1; linarith
    sorry

end
end CWComplex

section
  variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

  #check ContinuousMap.liftCover -- gluing lemma

  #check continuous_of_discreteTopology
  #check ContinuousMap
  #check Continuous -- isOpen_preimage : ∀ s, IsOpen s → IsOpen (f ⁻¹' s)

  example (f : X → Y) (isClosed_preimage : ∀ s, IsClosed s → IsClosed (f ⁻¹' s)) : Continuous f := by
    exact continuous_iff_isClosed.mpr isClosed_preimage
end

section
  #check Finset

  variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

  variable {ι : Type*} [Finite ι] (S : ι → Set α) (φ : ∀ i : ι, C(S i, β))
  (hφ : ∀ (i j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩)
  (hS_cover : ∀ x : α, ∃ i, x ∈ S i) (hS_closed : ∀ i, IsClosed (S i))

  noncomputable def liftCover_closed : C(α, β) :=
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

  #check Set.iUnionLift
  #check Set.liftCover
  #check ContinuousMap.liftCover
  #check Set.mem_image_val_of_mem
  #check Set.liftCover_of_mem
  #check Set.iUnion
  #check Set.iUnion_inter
  #check isClosed_iUnion_of_finite
end


-- variable {X : CWComplex}
-- #check (X : TopCat)
