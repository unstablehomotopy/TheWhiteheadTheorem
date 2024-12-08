import Mathlib.Topology.CWComplex
import Mathlib.Topology.Homotopy.HomotopyGroup


open scoped Topology TopCat ENNReal

section pDisk

universe u

variable (n : ℤ) (p q : ℝ≥0∞) [hp : Fact (1 ≤ p)] [hq : Fact (1 ≤ q)]

/-- The unit disk in `ℝⁿ` based on the `Lᵖ` norm, where `p ≥ 1`.  -/
def pDisk : TopCat.{u} :=
  TopCat.of <| ULift <| Metric.closedBall (0 : PiLp p fun (_ : Fin n.toNat) ↦ ℝ) 1

namespace pDisk

-- Note: need to declare the instances manually because `pDisk` and `TopCat` are not `abbrev`s.
instance instT1Space : T1Space (pDisk n p) :=
  letI : T1Space (ULift _) := inferInstance; ‹_›

noncomputable instance instPseudoMetricSpace : PseudoMetricSpace (pDisk n p) :=
  letI : PseudoMetricSpace (ULift _) := inferInstance; ‹_›

lemma dist_eq (x y : pDisk n p) : dist x y = dist x.down.val y.down.val :=
  rfl

/-- Use `0` to denote the center of the disk. -/
instance : OfNat (pDisk n p) 0 where
  ofNat := ⟨⟨0, Metric.mem_closedBall_self zero_le_one⟩⟩

lemma zero_eq : 0 = (0 : pDisk n p).down.val :=
  rfl

lemma eq_zero_iff (x : pDisk n p) : x = 0 ↔ x.down.val = 0 :=
  ⟨fun h ↦ by subst h; rfl, fun h ↦ by obtain ⟨x, _⟩ := x; congr⟩

/-- Map `x` to `(‖x‖_p / ‖x‖_q) • x`.
Note that division by zero evaluates to zero (see `toQDisk_zero`). -/
noncomputable def toQDisk : pDisk n p → pDisk n q
  | ⟨x, hx⟩ => ⟨ (‖x‖ * ‖WithLp.equiv q (Fin n.toNat → ℝ) |>.symm x‖⁻¹) • x, by
      simp only [Metric.mem_closedBall, dist_zero_right] at *
      simp only [norm_smul, norm_mul, Real.norm_eq_abs, abs_norm, norm_inv]
      rw [mul_assoc]
      -- Note that the two occurrences of `‖x‖` in the goal
      -- `⊢ ‖x‖ * (‖(WithLp.equiv q (Fin n.toNat → ℝ)).symm x‖⁻¹ * ‖x‖) ≤ 1` are different.
      -- The first `‖x‖` is `@norm (PiLp p fun x => ℝ) SeminormedAddGroup.toNorm x : ℝ`
      -- The last `‖x‖` is `@norm (PiLp q fun x => ℝ) SeminormedAddGroup.toNorm x : ℝ`
      -- Hence the goal is interpreted as `‖x‖_p * (‖x‖_q⁻¹ * ‖x‖_q) ≤ 1`
      exact Left.mul_le_one_of_le_of_le hx inv_mul_le_one (norm_nonneg _) ⟩

/-- `pDisk.toQDisk` maps `0` to `0`.
Note that division by zero evaluates to zero, due to `GroupWithZero.inv_zero`. -/
lemma toQDisk_zero : pDisk.toQDisk n p q 0 = 0 := by
  unfold toQDisk
  simp only [norm_zero, WithLp.equiv_symm_zero, inv_zero, mul_zero, smul_zero]
  congr

/-- The map `toQDisk` has a left inverse. -/
lemma toPDisk_comp_toQDisk x : toQDisk n q p (toQDisk n p q x) = x := by
  unfold toQDisk
  by_cases hx0 : x = 0
  · simp only [hx0, norm_zero, WithLp.equiv_symm_zero, inv_zero, mul_zero, smul_zero, eq_zero_iff]
  split; next _ y hy hfx =>
    rcases x with ⟨x, _⟩
    replace hx0 : x ≠ 0 := fun h ↦ hx0 (by congr)
    replace hfx := congrArg ULift.down hfx
    simp only [Subtype.mk.injEq] at hfx
    congr
    simp only [← hfx, WithLp.equiv_symm_smul]
    simp only [norm_smul, norm_mul, norm_norm, norm_inv, mul_inv_rev, inv_inv, smul_smul]
    rw [mul_assoc ‖x‖]
    conv in ‖x‖ * _ => arg 2; equals 1 => exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)
    simp only [mul_one, ← mul_assoc]
    conv in ‖x‖ * _ => equals 1 => exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx0)
    rw [one_mul, mul_assoc _ _ ‖x‖, @inv_mul_cancel₀ _ _ ‖x‖ (norm_ne_zero_iff.mpr hx0), mul_one]
    conv_lhs => arg 1; equals 1 => exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx0)
    rw [one_smul]

/-- The map `toQDisk` is continuous at `0`. -/
lemma continuousAt_toQDisk_zero : ContinuousAt (toQDisk n p q) 0 := by
  apply continuousAt_of_locally_lipschitz (_ : 0 < (1 : ℝ)) 1
  swap; norm_num
  intro ⟨x, hx⟩ h
  rw [toQDisk_zero]
  simp only [dist_eq, ← zero_eq, dist_zero_right, one_mul] at *
  simp only [toQDisk, norm_smul, norm_mul, norm_norm, norm_inv]
  by_cases hx0 : x = 0
  · simp only [hx0, norm_zero, WithLp.equiv_symm_zero, inv_zero, mul_zero, le_refl]
  rw [mul_assoc, mul_le_iff_le_one_right (norm_pos_iff.mpr hx0)]
  exact inv_mul_le_one

/-- The map `toQDisk` is continuous on `{x | x ≠ 0}`. -/
lemma continuousOn_toQDisk_nonzero : ContinuousOn (toQDisk n p q) {x | x ≠ 0} := by
  apply continuousOn_iff_continuous_restrict.mpr
  unfold Set.restrict toQDisk
  simp only [ne_eq, Set.coe_setOf, Set.mem_setOf_eq]
  refine continuous_uLift_up.comp <| Continuous.subtype_mk ?_ _
  refine Continuous.smul ?_ (continuous_uLift_down.comp continuous_subtype_val).subtype_val
  apply Continuous.mul (continuous_uLift_down.comp continuous_subtype_val).subtype_val.norm
  conv_rhs => intro x; rw [inv_eq_one_div]
  apply Continuous.div continuous_const
  · apply Continuous.norm
    apply @PiLp.continuous_equiv_symm _ _ (fun _ ↦ ℝ) |>.comp -- deleting this line results in deterministic timeout
    exact continuous_uLift_down.comp continuous_subtype_val |>.subtype_val
  intro ⟨x, hx0⟩ h
  simp only [norm_eq_zero] at h
  change x.down.val = 0 at h
  rw [← eq_zero_iff] at h
  exact hx0 h

/-- The map `toQDisk` is continuous. -/
lemma continuous_toQDisk : Continuous (toQDisk n p q) :=
  continuous_iff_continuousAt.mpr fun ⟨x, hx⟩ ↦ by
    by_cases hx0 : x = 0
    · subst hx0
      exact continuousAt_toQDisk_zero n p q
    exact (continuousOn_toQDisk_nonzero n p q).continuousAt
      (IsOpen.mem_nhds (IsClosed.not isClosed_singleton) fun h ↦ by
        simp only [eq_zero_iff] at h
        exact hx0 h)

/-- `pDisk n p` (the unit disk in `ℝⁿ` based on the `Lᵖ` norm) is homeomorphic to
`pDisk n q` (the unit disk in `ℝⁿ` based on the `L^q` norm). -/
noncomputable def homeoQDisk : pDisk n p ≃ₜ pDisk n q where
  toFun := toQDisk n p q
  invFun := toQDisk n q p
  left_inv := toPDisk_comp_toQDisk n p q
  right_inv := toPDisk_comp_toQDisk n q p
  continuous_toFun := continuous_toQDisk n p q
  continuous_invFun := continuous_toQDisk n q p

end pDisk

end pDisk

-- noncomputable def diskHomeoPDisk : 𝔻 n ≃ₜ pDisk n 2 where
--   toFun := id
--   -- invFun := id
--   left_inv := congrFun rfl
--   right_inv := congrFun rfl
--   -- continuous_toFun := continuous_id
--   -- continuous_invFun := continuous_id

/-- Auxiliary theorem used in `largeCubeHomeoPDisk`. -/
theorem Real.forall_le_of_iSup_le_of_bddAbove_range {ι : Sort*} {f : ι → ℝ} {a : ℝ}
    (hbdd : BddAbove (Set.range f)) (hf : ⨆ i, f i ≤ a) : ∀ (i : ι), f i ≤ a := fun i ↦ by
  cases (Set.range f).eq_empty_or_nonempty
  · exact Set.range_eq_empty_iff.mp ‹_› |>.false i |>.elim
  · exact Real.isLUB_sSup ‹_› hbdd |>.left (Set.mem_range_self i) |>.trans hf

/-- Auxiliary theorem used in `largeCubeHomeoPDisk`. -/
theorem Real.forall_le_of_iSup_le_of_finite_domain {ι : Type*} {f : ι → ℝ} {a : ℝ}
    [hfin : Finite ι] (hf : ⨆ i, f i ≤ a) : ∀ (i : ι), f i ≤ a := by
  refine forall_le_of_iSup_le_of_bddAbove_range ?_ hf
  cases isEmpty_or_nonempty ι
  · exact ⟨0, fun y hy ↦ (IsEmpty.exists_iff.mp hy).elim⟩
  · obtain ⟨i, hi⟩ := Finite.exists_max f
    exact ⟨f i, fun y hy ↦ by
      obtain ⟨j, hj⟩ := Set.mem_range.mp hy
      rw [← hj]; exact hi j⟩

/-- The large cube $[-1, 1]^n$ is homeomorphic to `pDisk n ∞` (the disk in `ℝⁿ` based on the `L∞` norm). -/
def largeCubeHomeoPDisk : (Fin n.toNat → Set.Icc (-1 : ℝ) (1 : ℝ)) ≃ₜ pDisk n ∞ where
  toFun := fun x ↦ ⟨⟨fun i ↦ x i, by
    simp only [Int.toNat_ofNat, Metric.mem_closedBall, PiLp.dist_eq_iSup]
    refine Real.iSup_le ?_ (by norm_num)
    intro i
    simp only [PiLp.zero_apply, dist_zero_right, Real.norm_eq_abs, abs_le]
    exact ⟨le_trans (by norm_num) (x i).prop.left, (x i).prop.right⟩ ⟩⟩
  invFun := fun ⟨⟨x, hx⟩⟩ i ↦ ⟨x i, by
    simp only [Metric.mem_closedBall, dist_zero_right, PiLp.norm_eq_ciSup, Real.norm_eq_abs] at hx
    -- Note: Here we cannot simply use `iSup_le_iff` because `ℝ` is not a `CompleteLattice`.
    -- We cannot use `Finset.le_sup` either, because although `ℝ` is a `SemilatticeSup`,
    -- it does not have a smallest element (i.e., we do not have `[OrderBot ℝ]`).
    -- With these restrictions, `Real.sSup_def`, the supremum of a set of real numbers,
    -- is defined in mathlib to be `0` if the set is not bounded from above or is empty.
    have := Real.forall_le_of_iSup_le_of_finite_domain hx i
    exact ⟨neg_le_of_abs_le this, le_of_max_le_left this⟩ ⟩
  left_inv := fun x ↦ rfl
  right_inv := fun ⟨⟨x, hx⟩⟩ ↦ rfl
  continuous_toFun := by
    refine continuous_uLift_up.comp (Continuous.subtype_mk ?_ _)
    exact continuous_pi fun i ↦ Continuous.subtype_val (continuous_apply i)
  continuous_invFun := continuous_pi fun i ↦
    (continuous_apply i).comp continuous_uLift_down.subtype_val |>.subtype_mk _

/-- The large cube $[-1, 1]^n$ is homeomorphic to the cube $[0, 1]^n$. -/
noncomputable def largeCubeHomeoCube {n : ℤ} :
    (Fin n.toNat → Set.Icc (-1 : ℝ) (1 : ℝ)) ≃ₜ I^ Fin n.toNat :=
  Homeomorph.piCongrRight fun _ ↦ iccHomeoI _ _ (by norm_num)

/-- The n-disk `𝔻 n` is homeomorphic to the cube $[0, 1]^n$. -/
noncomputable def diskHomeoCube : TopCat.disk.{u} n ≃ₜ (I^ Fin n.toNat) :=
  (pDisk.homeoQDisk.{u, u} n 2 ∞).trans <| largeCubeHomeoPDisk.symm.trans largeCubeHomeoCube
