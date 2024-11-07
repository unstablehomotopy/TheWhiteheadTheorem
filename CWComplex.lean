/-
Copyright (c) 2024 Elliot Dean Young and Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia, Elliot Dean Young
-/
import Mathlib.Topology.CWComplex
import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# CW-complexes

This file defines (relative) CW-complexes.

## Main definitions

* `RelativeCWComplex`: A relative CW-complex is the colimit of an expanding sequence of subspaces
  `sk i` (called the $(i-1)$-skeleton) for `i ≥ 0`, where `sk 0` (i.e., the $(-1)$-skeleton) is an
  arbitrary topological space, and each `sk (n + 1)` (i.e., the $n$-skeleton) is obtained from
  `sk n` (i.e., the $(n-1)$-skeleton) by attaching `n`-disks.

* `CWComplex`: A CW-complex is a relative CW-complex whose `sk 0` (i.e., $(-1)$-skeleton) is empty.

## References

* [R. Fritsch and R. Piccinini, *Cellular Structures in Topology*][fritsch-piccinini1990]
* The definition of CW-complexes follows David Wärn's suggestion on
  [Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Do.20we.20have.20CW.20complexes.3F/near/231769080).
-/

section GluingLemma

-- #check ContinuousMap.liftCover -- gluing lemma for an open cover

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

open unitInterval TopCat

abbrev Jar (n : ℤ) := 𝔻 (n + 1) × I
def jarMid (n : ℤ) := {⟨ ⟨⟨x, _⟩⟩, ⟨y, _⟩ ⟩ : Jar n | ‖x‖ ≤ 1 - y / 2}
def jarRim (n : ℤ) := {⟨ ⟨⟨x, _⟩⟩, ⟨y, _⟩ ⟩ : Jar n | ‖x‖ ≥ 1 - y / 2}

def jarClosedCover (n : ℤ) : Fin 2 → Set (Jar n) := ![jarMid n, jarRim n]

lemma continuous_sub_div_two : Continuous fun (y : ℝ) ↦ 1 - y / 2 :=
  (continuous_sub_left _).comp <| continuous_mul_right _

lemma isClosed_jarMid (n : ℤ) : IsClosed (jarMid n) :=
  continuous_iff_isClosed.mp (continuous_uLift_down.subtype_val.norm.prodMap continuous_id)
    {⟨x, y, _⟩ : ℝ × I | x ≤ 1 - y / 2} <| isClosed_le continuous_fst <|
    continuous_sub_div_two.comp <| continuous_subtype_val.comp continuous_snd

lemma isClosed_jarRim (n : ℤ) : IsClosed (jarRim n) :=
  continuous_iff_isClosed.mp (continuous_uLift_down.subtype_val.norm.prodMap continuous_id)
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

-- The triangle involving the bottom (i.e., `𝔻 (n + 1)`) of the jar commutes.
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


noncomputable section -- change of base point (draft)

universe u

open scoped Topology TopCat

def disk (n : ℤ) : TopCat.{u} :=
  TopCat.of <| ULift <| Metric.closedBall (0 : EuclideanSpace ℝ (Fin n.toNat)) 1  -- `L^2` norm

def cube (n : ℤ) : TopCat.{u} :=
  TopCat.of <| ULift <| { x : Fin n.toNat → ℝ | ‖x‖ ≤ 1 }  -- `L^∞` norm

set_option diagnostics true
-- example (x : EuclideanSpace ℝ (Fin 2)) : ℝ := if x = 0 then 1 else 2 -- failed to synthesize Decidable (x = 0)
example (x : (Fin 2) → ℝ) : ℝ := if x = 0 then 1 else 2
set_option diagnostics false

#check ContinuousAt
#check Continuous.continuousAt
#check ContinuousAt.continuousWithinAt
#check continuousAt_def
#check continuousAt_const_smul_iff
#check continuousAt_update_of_ne
#check continuousAt_update_same
#check continuousAt_apply
#check continuousAt_iff_ultrafilter

#check continuousAt_congr
#check continuousAt_codRestrict_iff
#check continuousOn_iff_continuous_restrict
#check continuousWithinAt_iff_continuousAt_restrict
--#check ContinuousMap.continuous_restrict

-- #check continuousAt_of_locally_lipschitz
-- #check Metric.continuousWithinAt_iff
-- #check (inferInstance : PseudoMetricSpace (EuclideanSpace ℝ (Fin 2)))
-- #check (inferInstance : PseudoMetricSpace (disk 2))  -- fail

#check continuousAt_of_tendsto_nhds
#check ContinuousAt.comp_continuousWithinAt
#check ContinuousOn.continuousAt
#check continuousOn_iff

section -- continuity of if-then-else functions

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

lemma continuousOn_of_continuous_subspace (A : Set X) [∀ x, Decidable (x ∈ A)]
    (f : C({x // x ∈ A}, Y)) (g : X → Y) :
    ContinuousOn (fun x ↦ if h : x ∈ A then f ⟨x, h⟩ else g x) A :=
  continuousOn_iff.mpr fun x hxA t ht hft ↦ by
    simp only [hxA, ↓reduceDIte] at hft
    have := @Continuous.continuousAt _ _ _ _ _ ⟨x, hxA⟩ f.continuous_toFun
    have hf := continuousAt_def.mp this t (ht.mem_nhds hft)
    rw [ContinuousMap.toFun_eq_coe, mem_nhds_iff] at hf
    obtain ⟨u, hu, ⟨v, hv, hvu⟩, hxu⟩ := hf
    use v, hv
    constructor
    . rw [← hvu, Set.mem_preimage] at hxu
      exact hxu
    rintro a ⟨hav, haA⟩
    simp only [Set.mem_preimage, haA, ↓reduceDIte]
    apply hu
    rw [← hvu, Set.mem_preimage]
    exact hav

end -- continuity of if-then-else functions

section -- experiment with easier funcitons

--#check continuous_iff_continuousOn_univ
#check continuous_subtype_val
example : ContinuousOn (· + (1 : ℝ)) {x | x > 0} := by
  apply continuousOn_iff_continuous_restrict.mpr
  -- unfold Set.restrict; simp only
  exact (continuous_add_right 1).comp continuous_subtype_val
def f₁ (n : ℤ) : disk n → cube n
  | ⟨x, hx⟩ => ⟨x, by
      simp only [Metric.mem_closedBall, dist_zero_right] at hx
      have lip := PiLp.lipschitzWith_equiv 2 _ x 0
      simp [edist_dist] at lip
      exact lip.trans hx⟩
lemma continuous_f₁ (n : ℤ) : Continuous (f₁ n) := by
  refine continuous_uLift_up.comp ?_
  refine Continuous.subtype_mk ?_ _
  -- refine Continuous.subtype_val ?_
  exact continuous_uLift_down.subtype_val
example (n : ℤ) : ContinuousOn (f₁ n) { ⟨x, _⟩ | ¬∀ i, x i = 0 } := by
  apply continuousOn_iff_continuous_restrict.mpr
  -- unfold Set.restrict
  exact (continuous_f₁ n).comp continuous_subtype_val
def f₂ (n : ℤ) : disk n → cube n
  | ⟨x, hx⟩ => ⟨‖x‖ • x, sorry⟩
#check Continuous.smul (Continuous.norm continuous_id) continuous_id
#check Continuous.prod_mk (Continuous.norm continuous_id) continuous_id
#check Continuous.norm continuous_id
#check Continuous.subtype_val
lemma continuous_f₂ (n : ℤ) : Continuous (f₂ n) := by
  refine continuous_uLift_up.comp ?_
  refine Continuous.subtype_mk ?_ _
  -- refine Continuous.smul ?_ ?_
  exact Continuous.smul (continuous_uLift_down.subtype_val.norm) continuous_uLift_down.subtype_val
def f₃ (n : ℤ) : disk n → cube n
  | ⟨x, hx⟩ => ⟨‖WithLp.equiv 2 _ x‖ • x, sorry⟩
#check PiLp.continuous_equiv 2
#check @PiLp.continuous_equiv 2 (Fin 5) (fun _ ↦ ℝ)
lemma continuous_f₃ (n : ℤ) : Continuous (f₃ n) := by
  refine continuous_uLift_up.comp ?_
  refine Continuous.subtype_mk ?_ _
  refine Continuous.smul ?_ ?_
  · refine Continuous.norm ?_
    --refine (@PiLp.continuous_equiv _ _ (fun _ ↦ ℝ)).comp ?_
    exact continuous_uLift_down.subtype_val
  exact continuous_uLift_down.subtype_val
lemma continuousOn_f₃ (n : ℤ) : ContinuousOn (f₃ n) { ⟨x, _⟩ | ¬∀ i, x i = 0 } := by
  apply continuousOn_iff_continuous_restrict.mpr
  refine continuous_uLift_up.comp ?_
  refine Continuous.subtype_mk ?_ _
  refine Continuous.smul ?_ ?_
  · refine Continuous.norm ?_
    -- refine (@PiLp.continuous_equiv _ _ (fun _ ↦ ℝ)).comp ?_
    exact (continuous_uLift_down.comp continuous_subtype_val).subtype_val
  exact (continuous_uLift_down.comp continuous_subtype_val).subtype_val
end -- experiment with easier funcitons

def diskToCube (n : ℤ) : disk n → cube n
  | ⟨x, hx⟩ => if ∀ i, x i = 0 then ⟨0, by simp [cube]⟩ else
      ⟨ (‖x‖ * ‖WithLp.equiv 2 _ x‖⁻¹) • x, by  -- (‖x‖₂ / ‖x‖_∞) • x
        simp only [Set.mem_setOf_eq, norm_smul, norm_mul, norm_norm, norm_inv]
        rw [mul_assoc]
        simp only [Metric.mem_closedBall, dist_zero_right] at hx
        exact Left.mul_le_one_of_le_of_le hx inv_mul_le_one (norm_nonneg _)⟩

lemma continuousOn_diskToCube (n : ℤ) : ContinuousOn (diskToCube n) { ⟨x, _⟩ | ¬∀ i, x i = 0 } := by
  apply continuousOn_iff_continuous_restrict.mpr
  unfold Set.restrict diskToCube
  refine continuous_uLift_up.comp ?_
  refine Continuous.subtype_mk ?_ _
  simp only [Set.coe_setOf, Set.mem_setOf_eq]
  sorry

lemma continuous_diskToCube (n : ℤ) : Continuous (diskToCube n) :=
  continuous_iff_continuousAt.mpr fun ⟨x, hx⟩ ↦ by
    by_cases hx0 : ∀ i, x i = 0
    . sorry
    sorry

def cubeToDisk (n : ℤ) : cube.{u} n → disk.{u} n
  | ⟨x, hx⟩ => if ∀ i, x i = 0 then ⟨0, by simp [disk]⟩ else
      ⟨ (‖x‖ * ‖(WithLp.equiv 2 _).symm x‖⁻¹) • x, by  -- (‖x‖_∞ / ‖x‖₂) • x
        simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_mul, norm_norm, norm_inv]
        rw [mul_assoc]
        exact Left.mul_le_one_of_le_of_le hx inv_mul_le_one (norm_nonneg _)⟩

lemma continuous_cubeToDisk (n : ℤ) : Continuous (cubeToDisk n) := by
  sorry

lemma cubeToDisk_comp_diskToCube (n : ℤ) : ∀ x, cubeToDisk n (diskToCube n x) = x := fun ⟨x, _⟩ ↦ by
  unfold cubeToDisk
  by_cases hx0 : ∀ i, x i = 0
  · simp [diskToCube, hx0]
    congr
    exact (PiLp.ext hx0).symm
  split
  next _ y hy hfx =>
    have hfx := congrArg ULift.down hfx
    simp [diskToCube, hx0] at hfx
    have hx0' : x ≠ 0 := fun h ↦ hx0 (congrFun h)
    have hf0 : ¬∀ i, y i = 0 := by simpa [← hfx, hx0, hx0', Decidable.not_forall.mp]
    split_ifs
    congr
    simp [← hfx, norm_smul, smul_smul]
    rw [mul_assoc ‖x‖]
    conv in ‖x‖ * _ => arg 2; equals 1 => exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr ‹_›)
    simp only [mul_one, ← mul_assoc]
    conv in ‖x‖ * _ => equals 1 => exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr ‹_›)
    rw [one_mul, mul_assoc _ _ ‖x‖, @inv_mul_cancel₀ _ _ ‖x‖ (norm_ne_zero_iff.mpr ‹_›), mul_one]
    conv_lhs => arg 1; equals 1 => exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr ‹_›)
    rw [one_smul]

lemma diskToCube_comp_cubeToDisk (n : ℤ) : ∀ x, diskToCube n (cubeToDisk n x) = x := fun ⟨x, _⟩ ↦ by
  unfold diskToCube
  by_cases hx0 : ∀ i, x i = 0
  . simp [cubeToDisk, hx0]
    congr
    aesop
  split
  next _ y hy hgx =>
    have hgx := congrArg ULift.down hgx
    simp [cubeToDisk, hx0] at hgx
    have hx0' : x ≠ 0 := fun h ↦ hx0 (congrFun h)
    have hg0 : ¬∀ i, y i = 0 := by simpa [← hgx, hx0, hx0', Decidable.not_forall.mp]
    split_ifs
    congr
    simp [← hgx, norm_smul, smul_smul]
    rw [mul_assoc ‖x‖]
    conv in ‖x‖ * _ => arg 2; equals 1 => exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr ‹_›)
    have : (x : Fin n.toNat → ℝ) → ‖(WithLp.equiv 2 _) x‖ = ‖x‖ := fun x ↦ rfl
    simp [this, norm_smul, ← mul_assoc]
    conv in ‖x‖ * _ => equals 1 => exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr ‹_›)
    rw [one_mul, mul_assoc _ _ ‖x‖, @inv_mul_cancel₀ _ _ ‖x‖ (norm_ne_zero_iff.mpr ‹_›), mul_one]
    conv_lhs => arg 1; equals 1 => exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr ‹_›)
    rw [one_smul]

def disk_homeo_cube (n : ℤ) : disk n ≃ₜ cube n where
  toFun := diskToCube n
  invFun := cubeToDisk n
  left_inv := cubeToDisk_comp_diskToCube n
  right_inv := diskToCube_comp_cubeToDisk n
  continuous_toFun := continuous_diskToCube n
  continuous_invFun := continuous_cubeToDisk n

end -- change of base point (draft)


section

open scoped ENNReal NNReal

open scoped Topology TopCat

noncomputable def Cube.center : I^α := fun _ ↦ ⟨1 / 2, by simp [inv_le_comm₀]⟩

noncomputable def Cube.ofDisk (n : ℕ) : (𝔻 n) → (I^ Fin n)
  | ⟨⟨x, hx⟩⟩ => if ∀ i, x i = 0 then Cube.center else fun i ↦ ⟨iSup x, sorry⟩

noncomputable def Cube.toDisk (n : ℕ) : (I^ Fin n) → (𝔻 n) := by
  sorry

def Cube.homeoDisk (n : ℕ) : (I^ Fin n) ≃ₜ (𝔻 n) where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  continuous_toFun := sorry
  continuous_invFun := sorry

end
