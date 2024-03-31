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

noncomputable def sphere : ℤ → TopCat
  | (n : ℕ) => TopCat.of <| Metric.sphere (0 : EuclideanSpace ℝ <| Fin <| n + 1) 1
  | _       => TopCat.of Empty

noncomputable def closedBall : ℤ → TopCat
  | (n : ℕ) => TopCat.of <| Metric.closedBall (0 : EuclideanSpace ℝ <| Fin n) 1
  | _       => TopCat.of Empty

notation "𝕊 "n => sphere n
notation "𝔻 "n => closedBall n

def sphereInclusion (n : ℤ) : (𝕊 n) → (𝔻 n + 1) :=
  match n with
  | Int.ofNat _   => fun ⟨pt, hpt⟩ => ⟨pt, le_of_eq hpt⟩
  | Int.negSucc _ => Empty.rec

theorem continuous_sphereInclusion (n : ℤ) : Continuous (sphereInclusion n) :=
  match n with
  | Int.ofNat _ => ⟨by
      intro _ ⟨t, ht, ht'⟩
      rw [isOpen_induced_iff]
      use t, ht
      rw [ht'.symm]
      tauto⟩
  | Int.negSucc n => ⟨by tauto⟩

def bundledSphereInclusion (n : ℤ) : TopCat.of (𝕊 n) ⟶ TopCat.of (𝔻 n + 1) :=
  ⟨sphereInclusion n, continuous_sphereInclusion n⟩

def sigmaSphereInclusion (n : ℤ) (cells : Type) :
    (Σ (_ : cells), 𝕊 n) → (Σ (_ : cells), 𝔻 n + 1) :=
  Sigma.map id fun _ x => sphereInclusion n x

theorem continuous_sigmaSphereInclusion (n : ℤ) (cells : Type) :
    Continuous (sigmaSphereInclusion n cells) := by
  apply Continuous.sigma_map
  intro _
  apply continuous_sphereInclusion

def bundledSigmaSphereInclusion (n : ℤ) (cells : Type) :
    TopCat.of (Σ (_ : cells), 𝕊 n) ⟶ TopCat.of (Σ (_ : cells), 𝔻 n + 1) :=
  ⟨sigmaSphereInclusion n cells, continuous_sigmaSphereInclusion n cells⟩

def sigmaAttachMap (X : TopCat) (n : ℤ) (cells : Type)
    (attach_maps : cells → C(𝕊 n, X)) :
    (Σ (_ : cells), 𝕊 n) → X :=
  fun ⟨i, x⟩ => attach_maps i x

theorem continuous_sigmaAttachMap (X : TopCat) (n : ℤ) (cells : Type)
    (attach_maps : cells → C(𝕊 n, X)) :
    Continuous (sigmaAttachMap X n cells attach_maps) := by
  apply continuous_sigma
  exact fun i => (attach_maps i).continuous_toFun

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
    rw [<- h]
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

def HomotopyExtensionProperty' {A X : TopCat} (i : A ⟶ X) : Prop :=
  ∀ (Y : TopCat) (f : X ⟶ Y) (H : TopCat.of (A × I) ⟶ Y), i ≫ f = inc₀ ≫ H →
  ∃ H' : TopCat.of (X × I) ⟶ Y, f = inc₀ ≫ H' ∧ H = prodMap i (𝟙 (TopCat.of I)) ≫ H'

-- def Jar (n : ℤ) := (𝔻 n + 1) × I

def jarMid (n : ℤ) : Set ((𝔻 n + 1) × I) :=
  match n + 1 with
  | Int.ofNat m   => {⟨⟨x, _⟩, ⟨y, _⟩⟩ : (𝔻 m) × I | ‖x‖ ≤ 1 - y / 2}
  | Int.negSucc _ => ∅

def jarRim (n : ℤ) : Set ((𝔻 n + 1) × I) :=
  match n + 1 with
  | Int.ofNat m   => {⟨⟨x, _⟩, ⟨y, _⟩⟩ : (𝔻 m) × I | ‖x‖ ≥ 1 - y / 2}
  | Int.negSucc _ => ∅

lemma continuous_sub_div_two : Continuous fun (y : ℝ) ↦ 1 - y / 2 :=
  (continuous_sub_left _).comp <| continuous_mul_right _

lemma isClosed_jarMid (n : ℤ) : IsClosed (jarMid n) := by
  unfold jarMid
  exact match n + 1 with
  | Int.ofNat m => continuous_iff_isClosed.mp (continuous_subtype_val.norm.prod_map continuous_id)
      {⟨x, y, _⟩ : ℝ × I | x ≤ 1 - y / 2} <| isClosed_le continuous_fst <|
      continuous_sub_div_two.comp <| continuous_subtype_val.comp continuous_snd
  | Int.negSucc _ => isClosed_empty

lemma isClosed_jarRim (n : ℤ) : IsClosed (jarRim n) := by
  unfold jarRim
  exact match n + 1 with
  | Int.ofNat m => continuous_iff_isClosed.mp (continuous_subtype_val.norm.prod_map continuous_id)
      {⟨x, y, _⟩ : ℝ × I | x ≥ 1 - y / 2} <| isClosed_le
      (continuous_sub_div_two.comp <| continuous_subtype_val.comp continuous_snd) continuous_fst
  | Int.negSucc _ => isClosed_empty

def jarClosedCover (n : ℤ) : Fin 2 → Set ((𝔻 n + 1) × I) := ![jarMid n, jarRim n]

lemma jarClosedCover_is_cover (n : ℤ) : ∀ (p : (𝔻 n + 1) × I), ∃ i, p ∈ jarClosedCover n i := by
  unfold jarClosedCover jarMid jarRim
  exact match n + 1 with
  | Int.ofNat m => fun ⟨⟨x, _⟩, ⟨y, _⟩⟩ ↦ by
    by_cases h : ‖x‖ ≤ 1 - y / 2
    . use 0; exact h
    . use 1; change ‖x‖ ≥ 1 - y / 2; linarith
  | Int.negSucc _ => fun p ↦ Empty.rec p.fst

noncomputable def jarMidProj (n : ℤ) : C(jarMid n, 𝔻 n + 1) := by
  unfold jarMid
  exact match n + 1 with
  | Int.ofNat m => {
      toFun := fun p ↦ {
        -- Note: pattern matching is done inside `toFun` to make `Continuous.subtype_mk` work
        val := match p with
          | ⟨⟨⟨x, _⟩, ⟨y, _⟩⟩, _⟩ => (2 / (2 - y)) • x,
        property := by
          obtain ⟨⟨⟨x, _⟩, ⟨y, _, _⟩⟩, hxy⟩ := p
          dsimp only [Int.ofNat_eq_coe, Set.coe_setOf, Set.mem_setOf_eq]
          rw [Metric.mem_closedBall]
          rw [dist_zero_right, norm_smul, norm_div, IsROrC.norm_ofNat, Real.norm_eq_abs]
          have : 0 < |2 - y| := lt_of_le_of_ne (abs_nonneg _) (abs_ne_zero.mpr (by linarith)).symm
          rw [← le_div_iff' (div_pos (by norm_num) this), one_div, inv_div]
          nth_rw 2 [← (@abs_eq_self ℝ _ 2).mpr (by norm_num)]
          rw [← abs_div, sub_div, div_self (by norm_num), le_abs]
          exact Or.inl hxy
      }
      continuous_toFun := ((continuous_smul.comp <| continuous_swap.comp <|
        continuous_subtype_val.prod_map <| continuous_const.div
          ((continuous_sub_left _).comp continuous_subtype_val) fun ⟨y, ⟨_, _⟩⟩ ↦ by
            rw [Function.comp_apply]; linarith).comp continuous_subtype_val).subtype_mk _
    }
  | Int.negSucc _ => continuousMapFromEmpty fun p ↦ p.val.fst

lemma jarRim_fst_ne_zero (n : ℕ) : ∀ p : jarRim n, ‖p.val.fst.val‖ ≠ 0 :=
  fun ⟨⟨⟨x, _⟩, ⟨y, _, _⟩⟩, hxy⟩ ↦ by
    conv => lhs; arg 1; dsimp
    change ‖x‖ ≥ 1 - y / 2 at hxy
    linarith

-- Note that `𝔻 0` is a singleton in `jarRim (-1) : Set ((𝔻 0) × I)`.
def emptyFromJarRimNegOne : jarRim (-1) → Empty :=
  fun ⟨⟨⟨x, _⟩, ⟨y, hy0, hy1⟩⟩, hxy⟩ ↦ by
    change ‖x‖ ≥ 1 - y / 2 at hxy
    change EuclideanSpace ℝ (Fin 0) at x
    rw [Subsingleton.eq_zero x, norm_zero] at hxy
    linarith

noncomputable def jarRimProjFst (n : ℤ) : C(jarRim n, 𝕊 n) :=
  match n with
  | Int.ofNat n => {
      toFun := fun p ↦ {
        val := match p with
          | ⟨⟨⟨x, _⟩, _⟩, _⟩ => (1 / ‖x‖) • x
        property := by
          obtain ⟨⟨⟨x, _⟩, ⟨y, _, _⟩⟩, hxy⟩ := p
          simp only [one_div, mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, norm_norm]
          change ‖x‖ ≥ 1 - y / 2 at hxy
          exact inv_mul_cancel (by linarith)
      }
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        exact continuous_smul.comp <| (Continuous.div continuous_const (continuous_norm.comp <|
          continuous_subtype_val.comp <| continuous_fst.comp <| continuous_subtype_val) <|
          jarRim_fst_ne_zero n).prod_mk <|
          continuous_subtype_val.comp <| continuous_fst.comp <| continuous_subtype_val
    }
  | Int.negSucc 0 => continuousMapFromEmpty emptyFromJarRimNegOne
  | Int.negSucc (_ + 1) => continuousMapFromEmpty fun p ↦ p.val.fst

noncomputable def jarRimProjSnd (n : ℤ) : C(jarRim n, I) :=
  match n with
  | Int.ofNat n => {
      toFun := fun pt ↦ {
        val := match pt with
          | ⟨⟨⟨x, _⟩, ⟨y, _⟩⟩, _⟩ => (y - 2) / ‖x‖ + 2
        property := by
          obtain ⟨⟨⟨x, hx⟩, ⟨y, _, _⟩⟩, hxy⟩ := pt
          simp only [Set.mem_Icc]
          rw [Metric.mem_closedBall, dist_zero_right] at hx
          change ‖x‖ ≥ 1 - y / 2 at hxy
          have : ‖x‖ > 0 := by linarith
          constructor
          all_goals rw [← add_le_add_iff_right (-2)]
          . rw [← neg_le_neg_iff, add_neg_cancel_right, zero_add, neg_neg]
            rw [← neg_div, neg_sub, div_le_iff (by assumption)]; linarith
          . rw [add_assoc, add_right_neg, add_zero, div_le_iff (by assumption)]; linarith
      }
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        exact (continuous_add_right _).comp <| Continuous.div
          ((continuous_sub_right _).comp <| continuous_subtype_val.comp <|
            continuous_snd.comp <| continuous_subtype_val)
          (continuous_norm.comp <| continuous_subtype_val.comp <|
            continuous_fst.comp <| continuous_subtype_val) <| jarRim_fst_ne_zero n
    }
  | Int.negSucc 0 => continuousMapFromEmpty emptyFromJarRimNegOne
  | Int.negSucc (_ + 1) => continuousMapFromEmpty fun p ↦ p.val.fst

noncomputable def jarRimProj (n : ℤ) : C(jarRim n, (𝕊 n) × I) :=
  ContinuousMap.prodMk (jarRimProjFst n) (jarRimProjSnd n)

variable (n : ℤ) {Y : TopCat}
  (f : TopCat.of (𝔻 n + 1) ⟶ Y) (H: TopCat.of ((𝕊 n) × I) ⟶ Y)
  (hf: bundledSphereInclusion n ≫ f = inc₀ ≫ H)

noncomputable def jarProj : ∀ i, C(jarClosedCover n i, Y) :=
  Fin.cons (f.comp (jarMidProj n)) <| Fin.cons (H.comp (jarRimProj n)) finZeroElim

lemma jarProj_compatible : ∀ (p : (𝔻 n + 1) × I)
    (hp0 : p ∈ jarClosedCover n 0) (hp1 : p ∈ jarClosedCover n 1),
    jarProj n f H 0 ⟨p, hp0⟩ = jarProj n f H 1 ⟨p, hp1⟩ :=
  match n with
  | Int.ofNat n => fun ⟨⟨x, hx⟩, ⟨y, hy0, hy1⟩⟩ hp0 hp1 ↦ by
      change f (jarMidProj n _) = H (jarRimProj n _)
      change ‖x‖ ≤ 1 - y / 2 at hp0
      change ‖x‖ ≥ 1 - y / 2 at hp1
      have : ‖x‖ = 1 - y / 2 := by linarith
      let q : 𝕊 n := ⟨ (2 / (2 - y)) • x, by
        simp only [mem_sphere_iff_norm, sub_zero, norm_smul, norm_div, IsROrC.norm_ofNat,
          Real.norm_eq_abs]
        rw [this, abs_of_pos (by linarith), div_mul_eq_mul_div, div_eq_iff (by linarith)]
        rw [mul_sub, mul_one, ← mul_comm_div, div_self (by norm_num), one_mul, one_mul] ⟩
      conv in jarMidProj n _ => equals bundledSphereInclusion n q =>
        unfold bundledSphereInclusion sphereInclusion
        conv => rhs; dsimp only [Int.ofNat_eq_coe, TopCat.coe_of]
      conv in jarRimProj n _ => equals @inc₀ (𝕊 n) q =>
        unfold jarRimProj jarRimProjFst jarRimProjSnd inc₀
        dsimp only [Int.ofNat_eq_coe, ContinuousMap.prod_eval, ContinuousMap.coe_mk]
        conv => rhs; change (q, ⟨0, by norm_num, by norm_num⟩)
        congr 2
        . congr 1
          rw [this, div_eq_div_iff (by linarith) (by linarith)]
          rw [one_mul, mul_sub, mul_one, ← mul_comm_div, div_self (by norm_num), one_mul]
        . rw [this, ← eq_sub_iff_add_eq, zero_sub, div_eq_iff (by linarith), mul_sub, mul_one]
          rw [mul_div, mul_div_right_comm, neg_div_self (by norm_num), ← neg_eq_neg_one_mul]
          rw [sub_neg_eq_add, add_comm]; rfl
      change (bundledSphereInclusion (Int.ofNat n) ≫ f).toFun q = (inc₀ ≫ H).toFun q
      rw [hf]
  | Int.negSucc 0 => fun p _ hp1 ↦ Empty.rec <| emptyFromJarRimNegOne ⟨p, hp1⟩
  | Int.negSucc (_ + 1) => fun p _ _ ↦ Empty.rec p.fst

noncomputable def jarHomotopyExtension : TopCat.of ((𝔻 n + 1) × I) ⟶ Y := by
  refine liftCoverClosed (jarClosedCover n) (jarProj n f H) ?_ (jarClosedCover_is_cover n) ?_
  . intro ⟨i, hi⟩ ⟨j, hj⟩ p hpi hpj
    interval_cases i <;> (interval_cases j <;> (try simp only [Fin.zero_eta, Fin.mk_one]))
    . exact jarProj_compatible n f H hf p hpi hpj
    . exact Eq.symm <| jarProj_compatible n f H hf p hpj hpi
  intro ⟨i, hi⟩; interval_cases i
  exact isClosed_jarMid n
  exact isClosed_jarRim n

-- def j0 {X : Type} [TopologicalSpace X] : C(X, X × I) := ⟨fun x => (x, 0), Continuous.Prod.mk_left 0⟩

def HomotopyExtensionProperty {A X : Type} [TopologicalSpace A] [TopologicalSpace X] (i : C(A, X)) : Prop :=
  ∀ (Y : Type) [TopologicalSpace Y] (f : C(X, Y)) (H : C(A × I, Y)), f ∘ i = H ∘ (., 0) →
  ∃ H' : C(X × I, Y), f = H' ∘ (., 0) ∧ H = H' ∘ Prod.map i id

-- theorem hep_sphereInclusion (n : ℤ) : HomotopyExtensionProperty (BundledSphereInclusion n) :=
--   match n with
--   | (n : ℕ) => sorry
--   | Int.negSucc n' => -- n = -(n' + 1)
--     if h_neg_one : n' = 0 then by
--       rw [h_neg_one]
--       intro Y _ f H hcomp
--       use ⟨fun (x, _) => f x, Continuous.fst' f.continuous_toFun⟩ -- f ∘ Prod.fst
--       simp
--       constructor
--       . ext x
--         simp
--       ext ⟨x, _⟩
--       tauto -- Empty.rec x
--     else by
--       have h_neg_one : n' > 0 := Nat.pos_of_ne_zero h_neg_one
--       have h_neg_one₁ : Int.negSucc n' < 0 := Int.negSucc_lt_zero n'
--       have h_neg_one₂ : Int.negSucc n' < 0 := Int.negSucc_lt_zero n'
--       have h_neg_one' : Int.negSucc n' + 1 < 0 := by
--         sorry
--       intro Y _ f H hcomp
--       -- have H' : Empty → Y := Empty.rec
--       -- have H' : (𝔻 (Int.negSucc n)) → Y := Empty.rec
--       let H' : (𝔻 Int.negSucc n') × I → Y := fun (x, _) => Empty.rec x
--       let H' : (𝔻 Int.negSucc n' + 1) × I → Y := by
--         intro (x, _)
--         unfold ClosedBall at x
--         sorry
--       sorry

-- theorem hep_sphereInclusion' (n : ℤ) : HomotopyExtensionProperty ⟨SphereInclusion n, continuous_sphereInclusion n⟩ :=
--   if h1 : n = -1 then by
--     rw [h1]
--     intro Y _ f H hcomp
--     use ⟨fun (x, _) => f x, Continuous.fst' f.continuous_toFun⟩ -- f ∘ Prod.fst
--     simp
--     constructor
--     . ext x
--       simp
--     ext ⟨x, _⟩
--     tauto
--   else if h2 : n + 1 < 0 then by
--     have ⟨m, hm⟩ := Int.eq_negSucc_of_lt_zero h2
--     intro Y _ f H hcomp
--     --rw [hm] at f
--     let φ (n : ℕ) : C(𝔻 Int.negSucc n, Y) := ⟨Empty.rec, by tauto⟩
--     let φ' (n : ℕ) : C((𝔻 Int.negSucc n) × I, Y) :=
--       ⟨fun (x, _) => φ n x, Continuous.fst' (φ n).continuous_toFun⟩
--     let H' : C((𝔻 n + 1) × I, Y) := by rw [hm]; exact φ' m
--     use H'
--     constructor
--     . ext x
--       dsimp
--       sorry
--     ext ⟨x, z⟩
--     simp
--     sorry
--   else by
--     have h3 : n ≥ 0 := by contrapose! h2; contrapose! h1; linarith
--     sorry

end HEP

end CWComplex

section
open CWComplex
open unitInterval

-- noncomputable def he_0'_BundledSphereInclusion
--     (f : TopCat.of (𝔻 1) ⟶ Y) (H: TopCat.of ((𝕊 0) × I) ⟶ Y)
--     (hf: BundledSphereInclusion 0 ≫ f = j0 ≫ H) : TopCat.of ((𝔻 1) × I) ⟶ Y := by
--   let X0 := {⟨⟨x, _⟩, ⟨y, _⟩⟩ : (𝔻 1) × I | ‖x‖ ≤ 1 - y / 2}
--   let X1 := {⟨⟨x, _⟩, ⟨y, _⟩⟩ : (𝔻 1) × I | ‖x‖ ≥ 1 - y / 2}
--   let H'0 : C(X0, 𝔻 1) := {
--     toFun := fun pt ↦ {
--       -- Note: pattern matching is done inside `toFun` to make `Continuous.subtype_mk` work
--       val := match pt with
--         | ⟨⟨⟨x, _⟩, ⟨y, _⟩⟩, _⟩ => (2 / (2 - y)) • x,
--       property := by
--         obtain ⟨⟨⟨x, _⟩, ⟨y, _, _⟩⟩, hxy⟩ := pt
--         simp [norm_smul]
--         have : 0 < |2 - y| := lt_of_le_of_ne (abs_nonneg _) (abs_ne_zero.mpr (by linarith)).symm
--         rw [← le_div_iff' (div_pos (by norm_num) this)]; simp
--         nth_rw 2 [← (@abs_eq_self ℝ _ 2).mpr (by norm_num)]
--         rw [← abs_div, le_abs, sub_div]; simp
--         exact Or.inl hxy
--     }
--     continuous_toFun := ((continuous_smul.comp <| continuous_swap.comp <|
--       continuous_subtype_val.prod_map <| continuous_const.div
--         ((continuous_sub_left _).comp continuous_subtype_val) fun ⟨y, ⟨_, _⟩⟩ ↦ by
--           dsimp; linarith).comp continuous_subtype_val).subtype_mk _
--   }
--   have : ∀ (pt : X1), ‖pt.val.fst.val‖ ≠ 0 := fun ⟨⟨⟨x, _⟩, ⟨y, _, _⟩⟩, hxy⟩ ↦ by
--     conv => lhs; arg 1; dsimp
--     change ‖x‖ ≥ 1 - y / 2 at hxy
--     linarith
--   let H'1_x : C(X1, 𝕊 0) := {
--     toFun := fun pt ↦ {
--       val := match pt with
--         | ⟨⟨⟨x, _⟩, _⟩, _⟩ => (1 / ‖x‖) • x
--       property := by
--         obtain ⟨⟨⟨x, _⟩, ⟨y, _, _⟩⟩, hxy⟩ := pt
--         simp [norm_smul]
--         change ‖x‖ ≥ 1 - y / 2 at hxy
--         exact inv_mul_cancel (by linarith)
--     }
--     continuous_toFun := by
--       refine Continuous.subtype_mk ?_ _
--       exact continuous_smul.comp <| (Continuous.div continuous_const (continuous_norm.comp <|
--         continuous_subtype_val.comp <| continuous_fst.comp <| continuous_subtype_val)
--         this).prod_mk <|
--         continuous_subtype_val.comp <| continuous_fst.comp <| continuous_subtype_val
--   }
--   let H'1_y : C(X1, I) := {
--     toFun := fun pt ↦ {
--       val := match pt with
--         | ⟨⟨⟨x, _⟩, ⟨y, _⟩⟩, _⟩ => (y - 2) / ‖x‖ + 2
--       property := by
--         obtain ⟨⟨⟨x, hx⟩, ⟨y, _, _⟩⟩, hxy⟩ := pt
--         simp; simp at hx
--         change ‖x‖ ≥ 1 - y / 2 at hxy
--         have : ‖x‖ > 0 := by linarith
--         constructor
--         all_goals rw [← add_le_add_iff_right (-2)]
--         . rw [← neg_le_neg_iff]; simp
--           rw [← neg_div, neg_sub, div_le_iff (by assumption)]; linarith
--         . rw [add_assoc, add_right_neg, add_zero, div_le_iff (by assumption)]; linarith
--     }
--     continuous_toFun := by
--       refine Continuous.subtype_mk ?_ _
--       exact (continuous_add_right _).comp <| Continuous.div
--         ((continuous_sub_right _).comp <| continuous_subtype_val.comp <|
--           continuous_snd.comp <| continuous_subtype_val)
--         (continuous_norm.comp <| continuous_subtype_val.comp <|
--           continuous_fst.comp <| continuous_subtype_val) this
--   }
--   let H'1 : C(X1, (𝕊 0) × I) := ⟨fun pt ↦ (H'1_x pt, H'1_y pt),
--     H'1_x.continuous_toFun.prod_mk H'1_y.continuous_toFun⟩
--   let S : Fin 2 → Set ((𝔻 1) × I) := ![X0, X1]
--   -- Notation for Fin.cons?
--   let φ : ∀ i, C(S i, Y) := Fin.cons (f.comp H'0) <| Fin.cons (H.comp H'1) finZeroElim
--   let hφ : ∀ (p : (𝔻 1) × I) (hp0 : p ∈ S 0) (hp1 : p ∈ S 1), φ 0 ⟨p, hp0⟩ = φ 1 ⟨p, hp1⟩ :=
--     fun ⟨⟨x, hx⟩, ⟨y, hy0, hy1⟩⟩ hp0 hp1 ↦ by
--       change f (H'0 _) = H (H'1 _)
--       change ‖x‖ ≤ 1 - y / 2 at hp0
--       change ‖x‖ ≥ 1 - y / 2 at hp1
--       have : ‖x‖ = 1 - y / 2 := by linarith
--       let q : 𝕊 0 := ⟨ (2 / (2 - y)) • x, by
--         simp [norm_smul]
--         rw [this, abs_of_pos (by linarith), div_mul_eq_mul_div, div_eq_iff (by linarith)]
--         rw [mul_sub, mul_one, ← mul_comm_div, div_self (by norm_num), one_mul, one_mul] ⟩
--       conv in H'0 _ => equals BundledSphereInclusion 0 q =>
--         unfold_let H'0 q
--         unfold BundledSphereInclusion SphereInclusion
--         conv => rhs; dsimp
--       conv in H'1 _ => equals @j0 (𝕊 0) q =>
--         unfold_let H'1 H'1_x H'1_y q
--         unfold j0
--         dsimp
--         conv => rhs; change (q, ⟨0, by norm_num, by norm_num⟩)
--         congr 2
--         . congr 1
--           rw [this, div_eq_div_iff (by linarith) (by linarith)]
--           rw [one_mul, mul_sub, mul_one, ← mul_comm_div, div_self (by norm_num), one_mul]
--         . rw [this, ← eq_sub_iff_add_eq, zero_sub, div_eq_iff (by linarith), mul_sub, mul_one]
--           rw [mul_div, mul_div_right_comm, neg_div_self (by norm_num), ← neg_eq_neg_one_mul]
--           rw [sub_neg_eq_add, add_comm]; rfl
--       change (BundledSphereInclusion 0 ≫ f).toFun q = (j0 ≫ H).toFun q
--       rw [hf]
--   apply liftCover_closed S φ
--   . intro ⟨i, hi⟩ ⟨j, hj⟩ p hpi hpj
--     interval_cases i <;> (interval_cases j <;> (try simp))
--     . exact hφ p hpi hpj
--     . exact Eq.symm <| hφ p hpj hpi
--   . intro ⟨⟨x, _⟩, ⟨y, _⟩⟩
--     by_cases h : ‖x‖ ≤ 1 - y / 2
--     . use 0; exact h
--     . use 1; change ‖x‖ ≥ 1 - y / 2; linarith
--   have : Continuous fun (y : ℝ) ↦ 1 - y / 2 := (continuous_sub_left _).comp <| continuous_mul_right _
--   intro ⟨i, hi⟩; interval_cases i
--   exact continuous_iff_isClosed.mp
--     (continuous_subtype_val.norm.prod_map continuous_id) {⟨x, y, _⟩ : ℝ × I | x ≤ 1 - y / 2} <|
--     isClosed_le continuous_fst <| this.comp <| continuous_subtype_val.comp continuous_snd
--   exact continuous_iff_isClosed.mp
--     (continuous_subtype_val.norm.prod_map continuous_id) {⟨x, y, _⟩ : ℝ × I | x ≥ 1 - y / 2} <|
--     isClosed_le (this.comp <| continuous_subtype_val.comp continuous_snd) continuous_fst

-- theorem hep_0' : HomotopyExtensionProperty' (BundledSphereInclusion 0) := by
--   unfold HomotopyExtensionProperty'
--   --unfold BundledSphereInclusion SphereInclusion
--   --simp
--   intro Y f H hf
--   -- ∃ H' : TopCat.of (X × I) ⟶ Y, f = j0 ≫ H' ∧ H = prod_map i (𝟙 (TopCat.of I)) ≫ H'
--   use he_0'_BundledSphereInclusion f H hf
--   constructor
--   .
--     sorry
--   . sorry

-- theorem hep_0 : HomotopyExtensionProperty (BundledSphereInclusion 0) := by
--   unfold HomotopyExtensionProperty
--   --unfold BundledSphereInclusion SphereInclusion
--   simp
--   intro Y instY f H hf
--   sorry

end
