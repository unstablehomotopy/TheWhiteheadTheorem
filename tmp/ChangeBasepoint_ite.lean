import Mathlib.Topology.CWComplex
import Mathlib.Topology.Homotopy.HomotopyGroup

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

#check ContinuousOn.congr_mono
def diskToCube' (n : ℤ) : disk n → cube n
  | ⟨x, hx⟩ =>
      ⟨ (‖x‖ * ‖WithLp.equiv 2 _ x‖⁻¹) • x, by  -- (‖x‖₂ / ‖x‖_∞) • x
        simp only [Set.mem_setOf_eq, norm_smul, norm_mul, norm_norm, norm_inv]
        rw [mul_assoc]
        simp only [Metric.mem_closedBall, dist_zero_right] at hx
        exact Left.mul_le_one_of_le_of_le hx inv_mul_le_one (norm_nonneg _)⟩

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
