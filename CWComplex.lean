/-
Copyright (c) 2024 Elliot Dean Young and Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia, Elliot Dean Young
-/

import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# CW-complexes

This file defines (relative) CW-complexes.

## Main definitions

* `RelativeCWComplex`: A relative CW-complex is the colimit of an expanding sequence of subspaces
`sk i` (called the `(i-1)`-skeleton) for `i ≥ 0`, where `sk 0` (i.e., the `(-1)`-skeleton) is an
arbitrary topological space, and each `sk (n+1)` (i.e., the `n`-skeleton) is obtained from `sk n`
(i.e., the `(n-1)`-skeleton) by attaching `n`-disks.

* `CWComplex`: A CW-complex is a relative CW-complex whose `sk 0` (i.e., `(-1)`-skeleton) is empty.

## References

The definition of CW-complexes follows David Wärn's suggestion at
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Do.20we.20have.20CW.20complexes.3F/near/231769080
-/

open CategoryTheory

universe u

namespace RelativeCWComplex

/-- The `n`-sphere is the set of points in ℝⁿ⁺¹ whose norm equals `1`,
endowed with the subspace topology. -/
noncomputable def sphere (n : ℤ) : TopCat.{u} :=
  TopCat.of <| ULift <| Metric.sphere (0 : EuclideanSpace ℝ <| Fin <| Int.toNat <| n + 1) 1

/-- The `n`-disk is the set of points in ℝⁿ whose norm is at most `1`,
endowed with the subspace topology. -/
noncomputable def disk (n : ℤ) : TopCat.{u} :=
  TopCat.of <| ULift <| Metric.closedBall (0 : EuclideanSpace ℝ <| Fin <| Int.toNat n) 1

/-- `𝕊 n` denotes the `n`-sphere. -/
scoped prefix:arg "𝕊 " => sphere

/-- `𝔻 n` denotes the `n`-disk. -/
scoped prefix:arg "𝔻 " => disk

/-- The inclusion map from the `n`-sphere to the `(n+1)`-disk -/
def sphereInclusion (n : ℤ) : 𝕊 n ⟶ 𝔻 (n + 1) where
  toFun := fun ⟨p, hp⟩ ↦ ⟨p, le_of_eq hp⟩
  continuous_toFun := ⟨fun t ⟨s, ⟨r, hro, hrs⟩, hst⟩ ↦ by
    rw [isOpen_induced_iff, ← hst, ← hrs]
    tauto⟩

variable {S D : ℤ → TopCat.{u}} (f : ∀ n, S n ⟶ D (n + 1))

/-- The inclusion map from the disjoint union of `S n` (boundary of generalized `(n+1)`-cells) to
the disjoint union of `D (n + 1)` (generalized `(n+1)`-cells) where both of the disjoint unions are
indexed by `cells` -/
def generalizedSigmaSphereInclusion (n : ℤ) (cells : Type) :
    TopCat.of (Σ (_ : cells), S n) ⟶ TopCat.of (Σ (_ : cells), D (n + 1)) where
  toFun := Sigma.map id fun _ x ↦ (f n).toFun x
  continuous_toFun := Continuous.sigma_map fun _ ↦ (f n).continuous_toFun

/-- Given an attaching map for each `S n` (boundary of a generalized `(n+1)`-cell), we construct
the attaching map for the disjoint union of all the `S n`. -/
def generalizedSigmaAttachMap (X : TopCat.{u}) (n : ℤ) (cells : Type)
    (attach_maps : cells → C(S n, X)) : TopCat.of (Σ (_ : cells), S n) ⟶ X where
  toFun := fun ⟨i, x⟩ ↦ attach_maps i x
  continuous_toFun := continuous_sigma fun i ↦ (attach_maps i).continuous_toFun

/-- A type witnessing that `X'` is obtained from `X` by attaching generalized `(n+1)`-cells, where
a generalized `(n+1)`-cell is given by `f n : S n ⟶ D (n + 1)`. -/
structure AttachGeneralizedCells (X X' : TopCat.{u}) (n : ℤ) where
  /-- The index type over the generalized `(n+1)`-cells -/
  cells : Type
  /-- For each generalized `(n+1)`-cell, we have an attaching map from its boundary to `X`. -/
  attach_maps : cells → C(S n, X)
  /-- `X'` is the pushout obtained from `X` along `sigmaAttachMap`. -/
  iso_pushout : X' ≅ Limits.pushout (generalizedSigmaSphereInclusion f n cells)
    (generalizedSigmaAttachMap X n cells attach_maps)

/-- The inclusion map from the disjoint union of `n`-spheres to the disjoint union of `(n+1)`-disks,
where both of the disjoint unions are indexed by `cells` -/
noncomputable abbrev sigmaSphereInclusion := generalizedSigmaSphereInclusion sphereInclusion

/-- Given an attaching map for each `n`-sphere, we construct the attaching map for the disjoint
union of the `n`-spheres. -/
abbrev sigmaAttachMap := @generalizedSigmaAttachMap sphere

/-- A type witnessing that `X'` is obtained from `X` by attaching `(n+1)`-disks -/
abbrev AttachCells := AttachGeneralizedCells sphereInclusion

end RelativeCWComplex

/-- A relative CW-complex contains an expanding sequence of subspaces `sk i` (called the
`(i-1)`-skeleton) for `i ≥ 0`, where `sk 0` (i.e., the `(-1)`-skeleton) is an arbitrary topological
space, and each `sk (n+1)` (i.e., the `n`-skeleton) is obtained from `sk n` (i.e., the
`(n-1)`-skeleton) by attaching `n`-disks. -/
structure RelativeCWComplex where
  /-- The skeletons. Note: `sk i` is usually called the `(i-1)`-skeleton in the math literature. -/
  sk : ℕ → TopCat.{u}
  /-- Each `sk (n+1)` (i.e., the `n`-skeleton) is obtained from `sk n` (i.e., the
  `(n-1)`-skeleton) by attaching `n`-disks. -/
  attach_cells (n : ℕ) : RelativeCWComplex.AttachCells (sk n) (sk (n + 1)) (n - 1)

/-- A CW-complex is a relative CW-complex whose `sk 0` (i.e., `(-1)`-skeleton) is empty. -/
structure CWComplex extends RelativeCWComplex.{u} where
  /-- `sk 0` (i.e., the `(-1)`-skeleton) is empty. -/
  sk_zero_empty : IsEmpty (sk 0)

namespace RelativeCWComplex

noncomputable section Topology

/-- The inclusion map from `X` to `X'`, given that `X'` is obtained from `X` by attaching
`(n+1)`-disks -/
def AttachCells.inclusion (X X' : TopCat.{u}) (n : ℤ) (att : AttachCells X X' n) : X ⟶ X' :=
  @Limits.pushout.inr TopCat _ _ _ X (sigmaSphereInclusion n att.cells)
    (sigmaAttachMap X n att.cells att.attach_maps) _ ≫ att.iso_pushout.inv

/-- The inclusion map from `sk n` (i.e., the `(n-1)`-skeleton) to `sk (n+1)` (i.e., the
`n`-skeleton) of a relative CW-complex -/
def inclusion (X : RelativeCWComplex.{u}) (n : ℕ) : X.sk n ⟶ X.sk (n + 1) :=
  RelativeCWComplex.AttachCells.inclusion (X.sk n) (X.sk (n + 1)) (n - 1) (X.attach_cells n)

/-- The topology on a relative CW-complex -/
def toTopCat (X : RelativeCWComplex.{u}) : TopCat.{u} :=
  Limits.colimit <| Functor.ofSequence <| inclusion X

instance : Coe RelativeCWComplex TopCat where coe X := toTopCat X

end Topology

end RelativeCWComplex


section GluingLemma

--#check ContinuousMap.liftCover -- gluing lemma for an open cover

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
      simp only [Set.mem_image, Set.mem_preimage, Subtype.exists, exists_and_right, exists_eq_right,
        Set.mem_inter_iff]
      conv => lhs; rhs; ext hxi; arg 2; equals Φ x => exact Eq.symm (Set.liftCover_of_mem hxi)
      tauto
    have : Φ ⁻¹' Y = ⋃ i, Subtype.val '' (φ i ⁻¹' Y) := by
      conv_rhs => ext x; arg 1; ext i; rw [this]
      conv_rhs => ext x; rw [← Set.iUnion_inter, H, Set.univ_inter]
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


namespace RelativeCWComplex

section HEP

open unitInterval

abbrev Jar (n : ℤ) := 𝔻 (n + 1) × I
def jarMid (n : ℤ) := {⟨ ⟨⟨x, _⟩⟩, ⟨y, _⟩ ⟩ : Jar n | ‖x‖ ≤ 1 - y / 2}
def jarRim (n : ℤ) := {⟨ ⟨⟨x, _⟩⟩, ⟨y, _⟩ ⟩ : Jar n | ‖x‖ ≥ 1 - y / 2}

def jarClosedCover (n : ℤ) : Fin 2 → Set (Jar n) := ![jarMid n, jarRim n]

lemma continuous_sub_div_two : Continuous fun (y : ℝ) ↦ 1 - y / 2 :=
  (continuous_sub_left _).comp <| continuous_mul_right _

lemma isClosed_jarMid (n : ℤ) : IsClosed (jarMid n) :=
  continuous_iff_isClosed.mp (continuous_uLift_down.subtype_val.norm.prod_map continuous_id)
    {⟨x, y, _⟩ : ℝ × I | x ≤ 1 - y / 2} <| isClosed_le continuous_fst <|
    continuous_sub_div_two.comp <| continuous_subtype_val.comp continuous_snd

lemma isClosed_jarRim (n : ℤ) : IsClosed (jarRim n) :=
  continuous_iff_isClosed.mp (continuous_uLift_down.subtype_val.norm.prod_map continuous_id)
    {⟨x, y, _⟩ : ℝ × I | x ≥ 1 - y / 2} <| isClosed_le
    (continuous_sub_div_two.comp <| continuous_subtype_val.comp continuous_snd) continuous_fst

noncomputable def jarMidProjToFun (n : ℤ) : jarMid.{u} n → disk.{u} (n + 1) := fun p ↦ ⟨{
  -- Note: pattern matching is done inside `toFun` to make `Continuous.subtype_mk` work
  val := match p with
    | ⟨⟨ ⟨⟨x, _⟩⟩, ⟨y, _⟩ ⟩, _⟩ => (2 / (2 - y)) • x,
  property := by
    obtain ⟨⟨ ⟨⟨x, _⟩⟩, ⟨y, _, _⟩ ⟩, hxy⟩ := p
    dsimp only [Int.ofNat_eq_coe, Set.coe_setOf, Set.mem_setOf_eq]
    rw [Metric.mem_closedBall]
    rw [dist_zero_right, norm_smul, norm_div, RCLike.norm_ofNat, Real.norm_eq_abs]
    have : 0 < |2 - y| := lt_of_le_of_ne (abs_nonneg _) (abs_ne_zero.mpr (by linarith)).symm
    rw [← le_div_iff₀' (div_pos (by norm_num) this), one_div, inv_div]
    nth_rw 2 [← (@abs_eq_self ℝ _ 2).mpr (by norm_num)]
    rw [← abs_div, sub_div, div_self (by norm_num), le_abs]
    exact Or.inl hxy }⟩

lemma continuous_jarMidProjToFun (n : ℤ) : Continuous (jarMidProjToFun.{u} n) := by
  refine continuous_uLift_up.comp ?_
  refine Continuous.subtype_mk ?_ _
  exact continuous_smul.comp <| Continuous.prod_mk
    (continuous_const.div ((continuous_sub_left _).comp <| continuous_subtype_val.comp <|
      continuous_snd.comp <| continuous_subtype_val) fun ⟨⟨ _, ⟨y, _, _⟩ ⟩, _⟩ ↦ by
        dsimp only [Function.comp_apply, ne_eq]; linarith)
    (continuous_subtype_val.comp <| continuous_uLift_down.comp <| continuous_fst.comp <|
      continuous_subtype_val)

noncomputable def jarMidProj (n : ℤ) : C(jarMid n, 𝔻 (n + 1)) :=
  ⟨jarMidProjToFun n, continuous_jarMidProjToFun n⟩

lemma jarRim_fst_ne_zero (n : ℤ) : ∀ p : jarRim n, ‖p.val.fst.down.val‖ ≠ 0 :=
  fun ⟨⟨ ⟨⟨x, _⟩⟩, ⟨y, _, _⟩ ⟩, hxy⟩ ↦ by
    conv => lhs; arg 1; dsimp
    change ‖x‖ ≥ 1 - y / 2 at hxy
    linarith

noncomputable def jarRimProjFstToFun (n : ℤ) : jarRim.{u} n → sphere.{u} n := fun p ↦ ⟨{
  val := match p with
    | ⟨⟨ ⟨⟨x, _⟩⟩, _ ⟩, _⟩ => (1 / ‖x‖) • x
  property := by
    obtain ⟨⟨ ⟨⟨x, _⟩⟩, ⟨y, yl, yr⟩ ⟩, hxy⟩ := p
    simp only [one_div, mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, norm_norm]
    change ‖x‖ ≥ 1 - y / 2 at hxy
    exact inv_mul_cancel₀ (by linarith) }⟩

lemma continuous_jarRimProjFstToFun (n : ℤ) : Continuous (jarRimProjFstToFun n) := by
  refine continuous_uLift_up.comp ?_
  refine Continuous.subtype_mk ?_ _
  exact continuous_smul.comp <| Continuous.prod_mk
    (Continuous.div continuous_const (continuous_norm.comp <| continuous_subtype_val.comp <|
      continuous_uLift_down.comp <| continuous_fst.comp <| continuous_subtype_val) <|
        jarRim_fst_ne_zero n)
    (continuous_subtype_val.comp <| continuous_uLift_down.comp <| continuous_fst.comp <|
      continuous_subtype_val)

noncomputable def jarRimProjFst (n : ℤ) : C(jarRim n, 𝕊 n) :=
  ⟨jarRimProjFstToFun n, continuous_jarRimProjFstToFun n⟩

noncomputable def jarRimProjSndToFun (n : ℤ) : jarRim n → I := fun p ↦ {
  val := match p with
    | ⟨⟨ ⟨⟨x, _⟩⟩, ⟨y, _⟩ ⟩, _⟩ => (y - 2) / ‖x‖ + 2
  property := by
    obtain ⟨⟨ ⟨⟨x, hx⟩⟩, ⟨y, _, _⟩ ⟩, hxy⟩ := p
    simp only [Set.mem_Icc]
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    change ‖x‖ ≥ 1 - y / 2 at hxy
    have : ‖x‖ > 0 := by linarith
    constructor
    all_goals rw [← add_le_add_iff_right (-2)]
    · rw [← neg_le_neg_iff, add_neg_cancel_right, zero_add, neg_neg]
      rw [← neg_div, neg_sub, div_le_iff₀ (by assumption)]; linarith
    · rw [add_assoc, add_neg_cancel, add_zero, div_le_iff₀ (by assumption)]; linarith}

lemma continuous_jarRimProjSndToFun (n : ℤ) : Continuous (jarRimProjSndToFun n) := by
  refine Continuous.subtype_mk ?_ _
  exact (continuous_add_right _).comp <| Continuous.div
    ((continuous_sub_right _).comp <| continuous_subtype_val.comp <|
      continuous_snd.comp <| continuous_subtype_val)
    (continuous_norm.comp <| continuous_subtype_val.comp <| continuous_uLift_down.comp <|
      continuous_fst.comp <| continuous_subtype_val) <| jarRim_fst_ne_zero n

noncomputable def jarRimProjSnd (n : ℤ) : C(jarRim n, I) :=
  ⟨jarRimProjSndToFun n, continuous_jarRimProjSndToFun n⟩

noncomputable def jarRimProj (n : ℤ) : C(jarRim n, (𝕊 n) × I) :=
  ContinuousMap.prodMk (jarRimProjFst n) (jarRimProjSnd n)

noncomputable def jarProj (n : ℤ) {Y : Type} [TopologicalSpace Y]
    (f : C(𝔻 (n + 1), Y)) (H: C((𝕊 n) × I, Y)) : ∀ i, C(jarClosedCover n i, Y) :=
  Fin.cons (f.comp (jarMidProj n)) <| Fin.cons (H.comp (jarRimProj n)) finZeroElim

lemma jarProj_compatible (n : ℤ) {Y : Type} [TopologicalSpace Y]
    (f : C(𝔻 (n + 1), Y)) (H: C((𝕊 n) × I, Y)) (hf: f ∘ sphereInclusion n = H ∘ (·, 0)) :
    ∀ (p : Jar n) (hp0 : p ∈ jarClosedCover n 0) (hp1 : p ∈ jarClosedCover n 1),
    jarProj n f H 0 ⟨p, hp0⟩ = jarProj n f H 1 ⟨p, hp1⟩ :=
  fun ⟨⟨⟨x, hx⟩⟩, ⟨y, hy0, hy1⟩⟩ hp0 hp1 ↦ by
    change f (jarMidProj n _) = H (jarRimProj n _)
    change ‖x‖ ≤ 1 - y / 2 at hp0
    change ‖x‖ ≥ 1 - y / 2 at hp1
    have : ‖x‖ = 1 - y / 2 := by linarith
    let q : 𝕊 n := ⟨ (2 / (2 - y)) • x, by
      simp only [mem_sphere_iff_norm, sub_zero, norm_smul, norm_div, RCLike.norm_ofNat,
        Real.norm_eq_abs]
      rw [this, abs_of_pos (by linarith), div_mul_eq_mul_div, div_eq_iff (by linarith)]
      rw [mul_sub, mul_one, ← mul_comm_div, div_self (by norm_num), one_mul, one_mul] ⟩
    conv in jarMidProj n _ => equals sphereInclusion n q =>
      unfold sphereInclusion jarMidProj jarMidProjToFun
      simp only [Fin.isValue, ContinuousMap.coe_mk]
      rw [← ContinuousMap.toFun_eq_coe]
    conv in jarRimProj n _ => equals (q, 0) =>
      unfold jarRimProj jarRimProjFst jarRimProjFstToFun jarRimProjSnd jarRimProjSndToFun
      dsimp only [Int.ofNat_eq_coe, ContinuousMap.prod_eval, ContinuousMap.coe_mk]
      conv => rhs; change (q, ⟨0, by norm_num, by norm_num⟩)
      congr 2
      · congr 2
        rw [this, div_eq_div_iff (by linarith) (by linarith)]
        rw [one_mul, mul_sub, mul_one, ← mul_comm_div, div_self (by norm_num), one_mul]
      · rw [this, ← eq_sub_iff_add_eq, zero_sub, div_eq_iff (by linarith), mul_sub, mul_one]
        rw [mul_div, mul_div_right_comm, neg_div_self (by norm_num), ← neg_eq_neg_one_mul]
        rw [sub_neg_eq_add, add_comm]; rfl
    change (f ∘ sphereInclusion n) q = (H ∘ (·, 0)) q
    rw [hf]

lemma jarProj_compatible' (n : ℤ) {Y : Type} [TopologicalSpace Y]
    (f : C(𝔻 (n + 1), Y)) (H: C((𝕊 n) × I, Y)) (hf: f ∘ sphereInclusion n = H ∘ (·, 0)) :
    ∀ (i j) (p : Jar n) (hpi : p ∈ jarClosedCover n i) (hpj : p ∈ jarClosedCover n j),
    jarProj n f H i ⟨p, hpi⟩ = jarProj n f H j ⟨p, hpj⟩ := by
  intro ⟨i, hi⟩ ⟨j, hj⟩ p hpi hpj
  interval_cases i <;> (interval_cases j <;> (try simp only [Fin.zero_eta, Fin.mk_one]))
  · exact jarProj_compatible n f H hf p hpi hpj
  · exact Eq.symm <| jarProj_compatible n f H hf p hpj hpi

lemma jarClosedCover_is_cover (n : ℤ) : ∀ (p : Jar n), ∃ i, p ∈ jarClosedCover n i :=
  fun ⟨⟨x, _⟩, ⟨y, _⟩⟩ ↦ by
    by_cases h : ‖x‖ ≤ 1 - y / 2
    · use 0; exact h
    · use 1; change ‖x‖ ≥ 1 - y / 2; linarith

lemma jarClosedCover_isClosed (n : ℤ) : ∀ i, IsClosed (jarClosedCover n i) := fun ⟨i, hi⟩ ↦ by
  interval_cases i
  exact isClosed_jarMid n
  exact isClosed_jarRim n

noncomputable def jarHomotopyExtension (n : ℤ) {Y : Type} [TopologicalSpace Y]
    (f : C(𝔻 (n + 1), Y)) (H: C((𝕊 n) × I, Y))
    (hf: f ∘ sphereInclusion n = H ∘ (·, 0)) : C((Jar n), Y) :=
  liftCoverClosed (jarClosedCover n) (jarProj n f H) (jarProj_compatible' n f H hf)
    (jarClosedCover_is_cover n) (jarClosedCover_isClosed n)

-- The triangle involving the bottom (i.e., `𝔻 n + 1`) of the jar commutes.
lemma jarHomotopyExtension_bottom_commutes (n : ℤ) {Y : Type} [TopologicalSpace Y]
    (f : C(𝔻 (n + 1), Y)) (H: C((𝕊 n) × I, Y))
    (hf: f ∘ sphereInclusion n = H ∘ (·, 0)) :
    ⇑f = jarHomotopyExtension n f H hf ∘ (·, 0) := by
  ext p
  change _ = jarHomotopyExtension n f H hf (p, 0)
  have hp : (p, 0) ∈ jarClosedCover n 0 := by
    obtain ⟨x, hx⟩ := p
    change ‖x‖ ≤ 1 - 0 / 2
    rw [zero_div, sub_zero]
    exact mem_closedBall_zero_iff.mp hx
  conv_rhs => equals (jarProj n f H 0) ⟨(p, 0), hp⟩ => apply liftCoverClosed_coe'
  simp only [Int.ofNat_eq_coe, jarProj, TopCat.coe_of, Fin.succ_zero_eq_one, Fin.cons_zero,
    ContinuousMap.comp_apply]
  congr
  change p = jarMidProjToFun n ⟨(p, 0), hp⟩
  obtain ⟨x, hx⟩ := p
  simp only [Int.ofNat_eq_coe, jarMidProjToFun, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, div_self, one_smul]

-- The triangle involving the wall (i.e., `𝕊 n × I`) of the jar commutes.
lemma jarHomotopyExtension_wall_commutes (n : ℤ) {Y : Type} [TopologicalSpace Y]
    (f : C(𝔻 (n + 1), Y)) (H: C((𝕊 n) × I, Y))
    (hf: f ∘ sphereInclusion n = H ∘ (·, 0)) :
    ⇑H = jarHomotopyExtension n f H hf ∘ Prod.map (sphereInclusion n) id := by
  ext ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  let q := (sphereInclusion n).toFun ⟨x, hx⟩
  change _ = jarHomotopyExtension n f H hf ⟨q, ⟨y, hy⟩⟩
  have hq : ⟨q, ⟨y, hy⟩⟩ ∈ jarClosedCover n 1 := by
    change ‖x‖ ≥ 1 - y / 2
    rw [mem_sphere_zero_iff_norm.mp hx]
    obtain ⟨_, _⟩ := hy
    linarith
  conv_rhs => equals (jarProj n f H 1) ⟨⟨q, ⟨y, hy⟩⟩, hq⟩ => apply liftCoverClosed_coe'
  simp only [jarProj, Fin.succ_zero_eq_one, Fin.cons_one, Fin.cons_zero, ContinuousMap.comp_apply]
  congr
  · dsimp only [jarRimProjFst, sphereInclusion, ContinuousMap.coe_mk, jarRimProjFstToFun, one_div,
      q]
    rw [mem_sphere_zero_iff_norm.mp hx, div_one, one_smul]
  · dsimp only [sphereInclusion, q]
    rw [mem_sphere_zero_iff_norm.mp hx, div_one, sub_add_cancel]

def HomotopyExtensionProperty {A X : Type u} [TopologicalSpace A] [TopologicalSpace X]
    (i : C(A, X)) : Prop :=
  ∀ {Y : Type} [TopologicalSpace Y] (f : C(X, Y)) (H : C(A × I, Y)), f ∘ i = H ∘ (·, 0) →
  ∃ H' : C(X × I, Y), ⇑f = ⇑H' ∘ (·, 0) ∧ ⇑H = ⇑H' ∘ Prod.map i id

theorem hep_sphereInclusion (n : ℤ) : HomotopyExtensionProperty (sphereInclusion.{u} n) :=
  fun f H hf ↦ ⟨jarHomotopyExtension n f H hf, jarHomotopyExtension_bottom_commutes n f H hf,
    jarHomotopyExtension_wall_commutes n f H hf⟩

end HEP

end RelativeCWComplex
