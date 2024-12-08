import Mathlib.Topology.CWComplex
import Mathlib.Topology.Homotopy.HomotopyGroup

#eval 1 / 0
#check HDiv.hDiv
set_option trace.Meta.synthInstance true
#check (inferInstance : HDiv ℝ ℝ ℝ)
set_option trace.Meta.synthInstance false
#check Nat.instDiv
#check Int.instDiv
#check Rat.instDiv


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

#check ContinuousOn.congr_mono


/-- Map `x` to `(‖x‖₂ / ‖x‖_∞) • x`. Note that division by zero evaluates to zero in mathlib. -/
def diskToCube (n : ℤ) : disk n → cube n
  | ⟨x, hx⟩ => ⟨ (‖x‖ * ‖WithLp.equiv 2 _ x‖⁻¹) • x, by
      simp only [Set.mem_setOf_eq, norm_smul, norm_mul, norm_norm, norm_inv]
      rw [mul_assoc]
      simp only [Metric.mem_closedBall, dist_zero_right] at hx
      exact Left.mul_le_one_of_le_of_le hx inv_mul_le_one (norm_nonneg _)⟩

/-- Map `x` to `(‖x‖_∞ / ‖x‖₂) • x`. Note that division by zero evaluates to zero in mathlib. -/
def cubeToDisk (n : ℤ) : cube.{u} n → disk.{u} n
  | ⟨x, hx⟩ => ⟨ (‖x‖ * ‖(WithLp.equiv 2 _).symm x‖⁻¹) • x, by
      simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_mul, norm_norm, norm_inv]
      rw [mul_assoc]
      exact Left.mul_le_one_of_le_of_le hx inv_mul_le_one (norm_nonneg _)⟩

lemma cubeToDisk_comp_diskToCube (n : ℤ) : ∀ x, cubeToDisk n (diskToCube n x) = x := fun ⟨x, _⟩ ↦ by
  unfold cubeToDisk
  by_cases hx0 : ∀ i, x i = 0
  · simp only [diskToCube, Set.coe_setOf, Set.mem_setOf_eq, WithLp.equiv_symm_smul]
    congr
    sorry
  split
  next _ y hy hfx =>
    have hfx := congrArg ULift.down hfx
    simp only [Set.coe_setOf, diskToCube, Set.mem_setOf_eq, Subtype.mk.injEq] at hfx
    have hx0' : x ≠ 0 := fun h ↦ hx0 (congrFun h)
    have hf0 : ¬∀ i, y i = 0 := by simpa [← hfx, hx0, hx0', Decidable.not_forall.mp]
    congr
    simp [← hfx, norm_smul, smul_smul]
    rw [mul_assoc ‖x‖]
    conv in ‖x‖ * _ => arg 2; equals 1 => exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr ‹_›)
    simp only [mul_one, ← mul_assoc]
    conv in ‖x‖ * _ => equals 1 => exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr ‹_›)
    rw [one_mul, mul_assoc _ _ ‖x‖, @inv_mul_cancel₀ _ _ ‖x‖ (norm_ne_zero_iff.mpr ‹_›), mul_one]
    conv_lhs => arg 1; equals 1 => exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr ‹_›)
    rw [one_smul]

-- lemma cubeToDisk_comp_diskToCube (n : ℤ) : ∀ x, cubeToDisk n (diskToCube n x) = x := fun ⟨x, _⟩ ↦ by
--   unfold cubeToDisk
--   by_cases hx0 : ∀ i, x i = 0
--   · simp [diskToCube, hx0]
--     congr
--     exact (PiLp.ext hx0).symm
--   split
--   next _ y hy hfx =>
--     have hfx := congrArg ULift.down hfx
--     simp [diskToCube, hx0] at hfx
--     have hx0' : x ≠ 0 := fun h ↦ hx0 (congrFun h)
--     have hf0 : ¬∀ i, y i = 0 := by simpa [← hfx, hx0, hx0', Decidable.not_forall.mp]
--     split_ifs
--     congr
--     simp [← hfx, norm_smul, smul_smul]
--     rw [mul_assoc ‖x‖]
--     conv in ‖x‖ * _ => arg 2; equals 1 => exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr ‹_›)
--     simp only [mul_one, ← mul_assoc]
--     conv in ‖x‖ * _ => equals 1 => exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr ‹_›)
--     rw [one_mul, mul_assoc _ _ ‖x‖, @inv_mul_cancel₀ _ _ ‖x‖ (norm_ne_zero_iff.mpr ‹_›), mul_one]
--     conv_lhs => arg 1; equals 1 => exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr ‹_›)
--     rw [one_smul]

-- lemma diskToCube_comp_cubeToDisk (n : ℤ) : ∀ x, diskToCube n (cubeToDisk n x) = x := fun ⟨x, _⟩ ↦ by
--   unfold diskToCube
--   by_cases hx0 : ∀ i, x i = 0
--   . simp [cubeToDisk, hx0]
--     congr
--     aesop
--   split
--   next _ y hy hgx =>
--     have hgx := congrArg ULift.down hgx
--     simp [cubeToDisk, hx0] at hgx
--     have hx0' : x ≠ 0 := fun h ↦ hx0 (congrFun h)
--     have hg0 : ¬∀ i, y i = 0 := by simpa [← hgx, hx0, hx0', Decidable.not_forall.mp]
--     split_ifs
--     congr
--     simp [← hgx, norm_smul, smul_smul]
--     rw [mul_assoc ‖x‖]
--     conv in ‖x‖ * _ => arg 2; equals 1 => exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr ‹_›)
--     have : (x : Fin n.toNat → ℝ) → ‖(WithLp.equiv 2 _) x‖ = ‖x‖ := fun x ↦ rfl
--     simp [this, norm_smul, ← mul_assoc]
--     conv in ‖x‖ * _ => equals 1 => exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr ‹_›)
--     rw [one_mul, mul_assoc _ _ ‖x‖, @inv_mul_cancel₀ _ _ ‖x‖ (norm_ne_zero_iff.mpr ‹_›), mul_one]
--     conv_lhs => arg 1; equals 1 => exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr ‹_›)
--     rw [one_smul]

def disk_homeo_cube (n : ℤ) : disk n ≃ₜ cube n where
  toFun := diskToCube n
  invFun := cubeToDisk n
  left_inv := cubeToDisk_comp_diskToCube n
  right_inv := sorry -- diskToCube_comp_cubeToDisk n
  continuous_toFun := sorry -- continuous_diskToCube n
  continuous_invFun := sorry -- continuous_cubeToDisk n

end -- change of base point (draft)
