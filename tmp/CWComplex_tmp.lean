/-
Copyright (c) 2024 Elliot Dean Young and Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia, Elliot Dean Young
-/

import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.CategoryTheory.Functor.OfSequence

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
scoped notation "𝕊 "n => sphere n

/-- `𝔻 n` denotes the `n`-disk. -/
scoped notation "𝔻 "n => disk n

/-- The inclusion map from the `n`-sphere to the `(n+1)`-disk -/
def sphereInclusion (n : ℤ) : (𝕊 n) ⟶ (𝔻 n + 1) where
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
  attach_cells : (n : ℕ) → RelativeCWComplex.AttachCells (sk n) (sk (n + 1)) (n - 1)

/-- A CW-complex is a relative CW-complex whose `sk 0` (i.e., `(-1)`-skeleton) is empty. -/
structure CWComplex extends RelativeCWComplex.{u} where
  /-- `sk 0` (i.e., the `(-1)`-skeleton) is empty. -/
  sk_zero_empty : sk 0 = TopCat.of (ULift Empty)

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
      conv_lhs => rhs; ext hxi; lhs; equals Φ x => exact Eq.symm (Set.liftCover_of_mem hxi)
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

abbrev Jar (n : ℤ) := (𝔻 n + 1) × I
def jarMid (n : ℤ) := {⟨ ⟨⟨x, _⟩⟩, ⟨y, _⟩ ⟩ : Jar n | ‖x‖ ≤ 1 - y / 2}
def jarRim (n : ℤ) := {⟨ ⟨⟨x, _⟩⟩, ⟨y, _⟩ ⟩ : Jar n | ‖x‖ ≥ 1 - y / 2}

def jarClosedCover (n : ℤ) : Fin 2 → Set (Jar n) := ![jarMid n, jarRim n]

lemma continuous_sub_div_two : Continuous fun (y : ℝ) ↦ 1 - y / 2 :=
  (continuous_sub_left _).comp <| continuous_mul_right _

lemma isClosed_jarMid (n : ℤ) : IsClosed (jarMid n) :=
  continuous_iff_isClosed.mp (continuous_uLift_down.subtype_val.norm.prod_map continuous_id)
    {⟨x, y, _⟩ : ℝ × I | x ≤ 1 - y / 2} <| isClosed_le continuous_fst <|
    continuous_sub_div_two.comp <| continuous_subtype_val.comp continuous_snd

-- lemma isClosed_jarMid' (n : ℤ) : IsClosed (jarMid.{u} n) := by
--   have f : Jar.{u} n → ℝ × I := fun p ↦ (‖p.1.down.val‖, id p.2)
--   have continuous_f : Continuous f := by sorry
--   exact continuous_iff_isClosed.mp (continuous_f)
--     {⟨x, y, _⟩ : ℝ × I | x ≤ 1 - y / 2} <| isClosed_le continuous_fst <|
--     continuous_sub_div_two.comp <| continuous_subtype_val.comp continuous_snd

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
    rw [← le_div_iff' (div_pos (by norm_num) this), one_div, inv_div]
    nth_rw 2 [← (@abs_eq_self ℝ _ 2).mpr (by norm_num)]
    rw [← abs_div, sub_div, div_self (by norm_num), le_abs]
    exact Or.inl hxy }⟩

lemma continuous_jarMidProjToFun (n : ℤ) : Continuous (jarMidProjToFun.{u} n) :=
  continuous_uLift_up.comp <|
    ((continuous_smul.comp <| continuous_swap.comp <| continuous_uLift_down.subtype_val.prod_map <|
      continuous_const.div ((continuous_sub_left _).comp continuous_subtype_val)
      fun ⟨y, _, _⟩ ↦ by rw [Function.comp_apply]; linarith).comp
    continuous_subtype_val).subtype_mk _

noncomputable def jarMidProj (n : ℤ) : C(jarMid n, 𝔻 n + 1) :=
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

lemma continuous_jarRimProjFstToFun (n : ℤ) : Continuous (jarRimProjFstToFun.{u} n) := by
  refine continuous_uLift_up.comp ?_
  refine Continuous.subtype_mk ?_ _
  exact continuous_smul.comp <| (Continuous.div continuous_const
    (continuous_uLift_down.subtype_val.fst.subtype_val.norm) <| jarRim_fst_ne_zero.{u} n).prod_mk <|
      continuous_uLift_down.subtype_val.fst.subtype_val

end HEP

end RelativeCWComplex
