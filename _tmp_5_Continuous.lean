import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.MetricSpace.Basic -- [TopologicalSpace ℝ]
import Mathlib.Analysis.InnerProductSpace.PiL2 -- EuclideanSpace

def NZReal := {x : ℝ | x ≠ 0}

#check Continuous.mul
lemma lem1 : Continuous fun (x : ℝ) ↦ x * x := continuous_id.mul continuous_id

#check Continuous.div
lemma lem2 : Continuous fun (x : NZReal) ↦ (1 : ℝ) / x :=
  continuous_const.div continuous_subtype_val fun ⟨x, hx⟩ ↦ hx

noncomputable def fun3 : NZReal → NZReal :=
  fun (⟨x, hx⟩ : NZReal) ↦ ⟨1 / x, div_ne_zero (by norm_num) hx⟩
lemma lem3 : Continuous fun3 :=
  Continuous.subtype_mk lem2 _

lemma lem4 : Continuous fun (⟨⟨x, hx⟩, ⟨y, hy⟩⟩ : NZReal × NZReal) ↦ (x * y) :=
  continuous_mul.comp <| continuous_subtype_val.prod_map continuous_subtype_val

-- lemma lem4' : Continuous fun (⟨⟨x, hx⟩, ⟨y, hy⟩⟩ : NZReal × NZReal) ↦ (x * y) :=
--   continuous_subtype_val.mul continuous_subtype_val
--
-- type mismatch
--   Continuous.mul continuous_subtype_val continuous_subtype_val
-- has type
--   Continuous fun x => ↑x * ↑x : Prop
-- but is expected to have type
--   Continuous fun x =>
--     match x with
--     | ({ val := x, property := hx }, { val := y, property := hy }) => x * y : Prop

lemma lem5 : Continuous fun (⟨⟨x, _⟩, ⟨y, _⟩⟩ : NZReal × NZReal) ↦ 1 / (x * y) :=
  continuous_const.div
  (continuous_mul.comp <| continuous_subtype_val.prod_map continuous_subtype_val)
  (fun ⟨⟨_, hx⟩, ⟨_, hy⟩⟩ ↦ mul_ne_zero hx hy)

noncomputable def fun6 : NZReal × NZReal → NZReal :=
  fun ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ↦ ⟨1 / (x * y),
    div_ne_zero (by norm_num) (mul_ne_zero hx hy)⟩
lemma lem6 : Continuous fun6 :=
  Continuous.subtype_mk lem5 _

------------------------------

example (n : ℕ) (x : EuclideanSpace ℝ <| Fin n) (hx : ‖x‖ ≠ 0) :
    (1 / ‖x‖) • x ∈ Metric.sphere 0 1 := by
  simp [norm_smul]
  exact inv_mul_cancel hx

#check inv_mul_cancel
#check mul_inv_cancel
#check inv_mul_eq_one
#check mul_inv_eq_one

example (n : ℕ) : Continuous fun (x : EuclideanSpace ℝ <| Fin n) ↦ ‖x‖ :=
  continuous_norm

example : Continuous fun (x : ℝ) ↦ Prod.mk x x := by
  refine Continuous.prod_mk continuous_id continuous_id

#check continuous_fst
#check continuous_inv
#check Continuous.div
#check continuous_div'

#check abs_eq_zero
#check norm_ne_zero_iff

example (x : ℝ) (_ : ¬ x = 0) : x ≠ 0 := by apply?

#check le_add_of_le_add_left
#check le_add_left
#check le_of_add_le_add_left
#check add_le_add_left
#check add_le_add_right

example (a b c : ℝ) : (a ≤ b ↔ a + c ≤ b + c) := Iff.symm (add_le_add_iff_right c)
example (a b : ℝ) : (a ≤ b ↔ -a ≥ -b) := Iff.symm neg_le_neg_iff
example (a : ℝ) : (a - a = 0) := sub_eq_zero_of_eq rfl

#check div_le_div
#check div_le_div''
#check div_le_div_flip
#check neg_div
#check neg_sub
#check div_one
#check div_le_iff
#check add_neg_cancel_comm
