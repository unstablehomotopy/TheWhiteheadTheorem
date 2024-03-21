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

def j0 {X : TopCat} : X ⟶ TopCat.of (X × I) := ⟨fun x => (x, 0), Continuous.Prod.mk_left 0⟩
def prod_map {W X Y Z : TopCat} (f : W ⟶ X) (g : Y ⟶ Z) : TopCat.of (W × Y) ⟶ TopCat.of (X × Z) :=
  ⟨Prod.map f g, Continuous.prod_map f.continuous_toFun g.continuous_toFun⟩
def HomotopyExtensionProperty' {A X : TopCat} (i : A ⟶ X) : Prop :=
  ∀ Y : TopCat, ∀ f : X ⟶ Y, ∀ H : TopCat.of (A × I) ⟶ Y, i ≫ f = j0 ≫ H →
  ∃ H' : TopCat.of (X × I) ⟶ Y, f = j0 ≫ H' ∧ H = prod_map i (𝟙 (TopCat.of I)) ≫ H'

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

  -- #check Finset
  -- #check Finite
  -- #check Set.iUnionLift
  -- #check Set.liftCover
  -- #check ContinuousMap.liftCover
  -- #check Set.mem_image_val_of_mem
  -- #check Set.liftCover_of_mem
  -- #check Set.iUnion
  -- #check Set.iUnion_inter
  -- #check isClosed_iUnion_of_finite
end

section
  #check liftCover_closed

  open CWComplex
  open unitInterval

  theorem hep_0' : HomotopyExtensionProperty' (BundledSphereInclusion 0) := by
    unfold HomotopyExtensionProperty'
    --unfold BundledSphereInclusion SphereInclusion
    simp
    intro Y f H hf
    -- ∃ H' : TopCat.of (X × I) ⟶ Y, f = j0 ≫ H' ∧ H = prod_map i (𝟙 (TopCat.of I)) ≫ H'
    let X0 := {⟨⟨x, _⟩, ⟨y, _⟩⟩ : (𝔻 1) × I | ‖x‖ ≤ 1 - y / 2}
    let X1 := {⟨⟨x, _⟩, ⟨y, _⟩⟩ : (𝔻 1) × I | ‖x‖ ≥ 1 - y / 2}

    -- have : (x y z : ℝ) → (hx : x > 0) → (h : x * y ≤ z) → (y ≤ z / x) :=
    --   fun x y z hx h ↦ by
    --     exact (le_div_iff' hx).mpr h
    -- have : (x : ℝ) → (h1 : 0 < x) → 0 < 2 / x := fun x h1 ↦ div_pos (by linarith) h1
    -- have : 3 < 5 := by decide
    -- have : (n : ℕ) → (x : EuclideanSpace ℝ (Fin n)) → (r : ℝ)
    --   → ‖r • x‖ = ‖r‖ * ‖x‖ := fun n x r ↦ norm_smul _ _

    -- have : Continuous fun (⟨x, y⟩ : (𝔻 1) × I) ↦ x := continuous_fst.comp continuous_id
    -- have : Continuous fun (⟨x, y⟩ : (𝔻 1) × I) ↦ Prod.mk y x := continuous_swap
    -- have : Continuous fun (⟨⟨x, _⟩, ⟨y, _⟩⟩ : (𝔻 1) × I) ↦ Prod.mk y x :=
    --    continuous_swap.comp (Continuous.prod_map continuous_subtype_val continuous_subtype_val)
    -- have : Continuous fun (⟨x, y⟩ : ℝ × (EuclideanSpace ℝ <| Fin 1)) ↦ x • y := continuous_smul
    -- have : Continuous fun (⟨x, y⟩ : (𝔻 1) × I) ↦ y.val • x.val := continuous_smul.comp <|
    --   continuous_swap.comp <| Continuous.prod_map continuous_subtype_val continuous_subtype_val
    -- have : Continuous fun (x : {x : ℝ | x ≠ 0}) ↦ (1 : ℝ) / x :=
    --   continuous_const.div continuous_subtype_val fun x ↦ unitsEquivNeZero.proof_2 ℝ x

    let H'0 : C(X0, (𝔻 1)) := {
      toFun := fun pt ↦ {
        -- Note: pattern matching is done inside `toFun` to make `Continuous.subtype_mk` work
        val := match pt with
          | ⟨⟨⟨x, _⟩, ⟨y, _⟩⟩, _⟩ => (2 / (2 - y)) • x,
        property := by
          obtain ⟨⟨⟨x, _⟩, ⟨y, _, _⟩⟩, hxy⟩ := pt
          simp [norm_smul]
          have : 0 < |2 - y| := lt_of_le_of_ne (abs_nonneg _) (abs_ne_zero.mpr (by linarith)).symm
          rw [← le_div_iff' (div_pos (by norm_num) this)]; simp
          nth_rw 2 [← (@abs_eq_self ℝ _ 2).mpr (by norm_num)]
          rw [← abs_div, le_abs, sub_div]; simp
          exact Or.inl hxy
      }
      continuous_toFun := by
        have : Continuous fun (y : ℝ) ↦ 2 - y := by continuity
        exact ((continuous_smul.comp <| continuous_swap.comp <| continuous_subtype_val.prod_map <|
          continuous_const.div (this.comp continuous_subtype_val) fun ⟨y, ⟨_, _⟩⟩ ↦ by
            simp; linarith).comp continuous_subtype_val).subtype_mk _
    }

    let H'1_x : C(X1, (𝕊 0)) := {
      toFun := fun pt ↦ {
        val := match pt with
          | ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, hxy⟩ => (1 / ‖x‖) • x
        property := by
          obtain ⟨⟨⟨x, _⟩, ⟨y, _, _⟩⟩, hxy⟩ := pt
          simp [norm_smul]
          change ‖x‖ ≥ 1 - y / 2 at hxy
          exact inv_mul_cancel (by linarith)
      }
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        exact continuous_smul.comp <| (Continuous.div continuous_const (continuous_norm.comp <|
          continuous_subtype_val.comp <| continuous_fst.comp <| continuous_subtype_val) fun pt ↦ by
            obtain ⟨⟨⟨x, _⟩, ⟨y, _, _⟩⟩, hxy⟩ := pt
            simp; change x ≠ 0; rw [← norm_ne_zero_iff]
            change ‖x‖ ≥ 1 - y / 2 at hxy
            linarith).prod_mk <|
          continuous_subtype_val.comp <| continuous_fst.comp <| continuous_subtype_val
    }

    let H'1 : C(X1, (𝕊 0) × I) := {
      toFun := fun pt ↦ match pt with
        | ⟨⟨⟨x, _⟩, ⟨y, _⟩⟩, _⟩ => ⟨
            ⟨(1 / ‖x‖) • x, by sorry⟩,
            ⟨(y - 2) / ‖x‖ + 2, sorry⟩
          ⟩,
      continuous_toFun := by
        sorry
    }

    -- have : Continuous fun (x : ℝ) ↦ ‖x‖ := continuous_norm
    --have : Continuous fun (⟨x, _⟩ : 𝔻 1) ↦ ‖x‖ := continuous_subtype_val.norm
    -- have : Continuous (id : ℝ → ℝ) := continuous_id
    -- let Z1 := {⟨x, y⟩ : ℝ × ℝ | x ≤ 1 - y / 2}
    -- let Z1' := {⟨x, ⟨y, hy⟩⟩ : ℝ × I | x ≤ 1 - y / 2}
    -- let Z1'' := {⟨⟨x, hx⟩, ⟨y, hy⟩⟩ : I × I | x ≤ 1 - y / 2}
    -- have : IsClosed Z1 := isClosed_le continuous_fst (by continuity)
    -- have : IsClosed Z1' := isClosed_le continuous_fst (by continuity)
    -- have : IsClosed Z1'' := isClosed_le (continuous_subtype_val.comp' continuous_fst) (by continuity)
    -- let Z2 := Metric.closedBall (0 : EuclideanSpace ℝ <| Fin 2) 1
    -- have : IsClosed Z2 := Metric.isClosed_ball

    have : Continuous fun (y : ℝ) ↦ 1 - y / 2 := by continuity
    have hX0 : IsClosed X0 := continuous_iff_isClosed.mp
      (continuous_subtype_val.norm.prod_map continuous_id) {⟨x, y, _⟩ : ℝ × I | x ≤ 1 - y / 2} <|
      isClosed_le continuous_fst <| this.comp <| continuous_subtype_val.comp continuous_snd
    have hX1 : IsClosed X1 := continuous_iff_isClosed.mp
      (continuous_subtype_val.norm.prod_map continuous_id) {⟨x, y, _⟩ : ℝ × I | x ≥ 1 - y / 2} <|
      isClosed_le (this.comp <| continuous_subtype_val.comp continuous_snd) continuous_fst

    sorry

  theorem hep_0 : HomotopyExtensionProperty (BundledSphereInclusion 0) := by
    unfold HomotopyExtensionProperty
    --unfold BundledSphereInclusion SphereInclusion
    simp
    intro Y instY f H hf
    sorry

  #check unitsEquivNeZero
  #check ContinuousDiv
  #check Continuous.div
  #check Continuous.div'
  #check continuous_div'
  #check continuous_inv
  #check Continuous.comp
  #check Continuous.comp'
  #check (fun (⟨x, hx⟩ : 𝔻 1) ↦ ‖x‖)
  #check continuous_swap
  #check ContinuousSMul
  #check ContinuousConstSMul
  #check Prod.continuousSMul
  #check Prod.continuousConstSMul
  #check Ring.uniformContinuousConstSMul

  #check norm_smul
  #check norm_div
  #check abs_eq_self
  #check abs_div
  #check le_abs
  #check add_div
  #check sub_div
  #check Real.norm_eq_abs
  #check abs_ne_zero.mpr
  #check one_div_pos

  #check isClosed_compl_iff
  #check isOpen_prod_iff
  #check isOpen_prod_iff'
  #check Metric.isClosed_ball
  #check isClosed_Iic
  #check isClosed_le
  #check OrderClosedTopology
  set_option trace.Meta.synthInstance true in
  #check OrderClosedTopology I
  set_option trace.Meta.synthInstance true in
  #check OrderClosedTopology ℝ
  set_option trace.Meta.synthInstance true in
  #check Continuous fun (x : ℝ) ↦ x * x
  #check Continuous.mul
end


-- variable {X : CWComplex}
-- #check (X : TopCat)
