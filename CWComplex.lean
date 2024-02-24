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

theorem continuous_SphereInclusion (n : ℤ) : Continuous (SphereInclusion n) :=
  match n with
  | Int.ofNat _ => ⟨by
      intro _ ⟨t, ht, ht'⟩
      rw [isOpen_induced_iff]
      use t, ht
      rw [ht'.symm]
      tauto⟩
  | Int.negSucc n => ⟨by tauto⟩

def SigmaSphereInclusion (n : ℤ) (cells : Type) :
    (Σ (_ : cells), 𝕊 n) → (Σ (_ : cells), 𝔻 n + 1) :=
  Sigma.map id fun _ x => SphereInclusion n x

theorem continuous_sigmaSphereInclusion (n : ℤ) (cells : Type) :
    Continuous (SigmaSphereInclusion n cells) := by
  apply Continuous.sigma_map
  intro _
  apply continuous_SphereInclusion

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

section
  variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  set_option trace.Meta.synthInstance true
  #check C(X × Y, X × Y)
  --#check C(X ×ˢ Y, X ×ˢ Y)
  open unitInterval
  #check C(X, X × I)
  #check (TopCat.of (X × I))
  --#check (X × TopCat.of I : TopCat)
end

open unitInterval

def j0 {X : TopCat} : X ⟶ TopCat.of (X × I) := ⟨fun x => (x, 0), Continuous.Prod.mk_left 0⟩
def j1 {X : TopCat} : X ⟶ TopCat.of (X × I) := ⟨fun x => (x, 1), Continuous.Prod.mk_left 1⟩

def j0' {X : Type} [TopologicalSpace X] : C(X, X × I) := ⟨fun x => (x, 0), Continuous.Prod.mk_left 0⟩
def j1' {X : Type} [TopologicalSpace X] : C(X, X × I) := ⟨fun x => (x, 1), Continuous.Prod.mk_left 1⟩

def tmp {X Y : TopCat} (f : X ⟶ Y) : TopCat.of (X × I) ⟶ TopCat.of (Y × I) :=
  ⟨fun (x, z) => (f x, z), Continuous.prod_map f.continuous_toFun continuous_id⟩
def tmp₁ {X Y : TopCat} (f : X ⟶ Y) : TopCat.of (X × I) ⟶ TopCat.of (Y × I) :=
  ⟨Prod.map f id, Continuous.prod_map f.continuous_toFun continuous_id⟩
def tmp' {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) : C(X × I, Y × I) := ⟨fun (x, z) => (f x, z),
    Continuous.prod_map f.continuous_toFun continuous_id⟩
def tmp'' {X Y X' Y' : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
  (f : C(X, Y)) (g : C(X', Y')) : C(X × X', Y × Y') := ⟨fun (x, y) => (f x, g y), Continuous.prod_map f.continuous_toFun g.continuous_toFun⟩
#print tmp'

def prod_map {W X Y Z : TopCat} (f : W ⟶ X) (g : Y ⟶ Z) : TopCat.of (W × Y) ⟶ TopCat.of (X × Z) :=
  ⟨fun (w, y) => (f w, g y), Continuous.prod_map f.continuous_toFun g.continuous_toFun⟩
def prod_map' {W X Y Z : Type} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  (f : C(W, X)) (g : C(Y, Z)) : C(W × Y, X × Z) := ⟨fun (w, y) => (f w, g y), Continuous.prod_map f.continuous_toFun g.continuous_toFun⟩

def homotopyExtensionProperty {A X : TopCat} (i : A ⟶ X) : Prop :=
  ∀ Y : TopCat, ∀ f : X ⟶ Y, ∀ H : TopCat.of (A × I) ⟶ Y, i ≫ f = j0 ≫ H →
  ∃ H' : TopCat.of (X × I) ⟶ Y, f = j0 ≫ H' ∧ H = prod_map i (𝟙 (TopCat.of I)) ≫ H'

def homotopyExtensionProperty' {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    (i : C(A, X)) : Prop :=
  ∀ Y : Type, [TopologicalSpace Y] → ∀ f : C(X, Y), ∀ H : C(A × I, Y), f ∘ i = H ∘ j0' →
  ∃ H' : C(X × I, Y), f = H' ∘ j0' ∧ H = H' ∘ prod_map' i ⟨id, continuous_id⟩

end
end CWComplex


-- variable {X : CWComplex}
-- #check (X : TopCat)
