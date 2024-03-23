import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.MetricSpace.Basic -- [TopologicalSpace ℝ]
import Mathlib.Analysis.InnerProductSpace.PiL2 -- EuclideanSpace
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Topology.Category.TopCat.Basic

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
example (a : ℝ) : (a + (-a) = 0) := by exact add_right_neg a
example (a : ℝ) : (a - a = 0) := sub_eq_zero_of_eq rfl

#check div_le_div
#check div_le_div''
#check div_le_div_flip
#check neg_div
#check neg_sub
#check div_one
#check div_le_iff
#check add_neg_cancel_comm

#check continuous_sub_right
#check continuous_add_right

example : Continuous fun (y : ℝ) => y / 2 := by apply?

#check List
#check Vector
#check Array
#check Fin.cases
#check Fin.cons
#check Fin.tuple0_le
#check FinVec.seq

example (n : ℕ) : ¬ n < 0 := by exact Nat.not_lt_zero n
-- example (x y : ℝ) (h1 : x ≤ y) (h2 : x ≥ y) : x = y := by exact
--   Real.partialOrder.proof_4 x y h1 h2

#check div_mul_comm
#check div_mul_eq_mul_div
#check eq_mul_inv_iff_mul_eq₀
#check mul_inv_eq_iff_eq_mul
#check div_eq_iff
#check abs_ne_zero

example (x : ℝ) (h : x > 0) : |x| = x := by exact abs_of_pos h
example (a b c : ℝ) : a * (b / c) = a / c * b := by exact (mul_comm_div a c b).symm
example (a b c : ℝ) : a * b / c = a / c * b := by exact mul_div_right_comm a b c

#check div_self

example (f g : ℝ → ℝ) (x : ℝ) : f (g (x)) = (f ∘ g) x := by exact rfl
#check Eq.trans

#check div_eq_div_iff

example (a b c : ℝ) (h : a + b = c) : a = c - b := eq_sub_of_add_eq h
example (a b c : ℝ) : a + b = c ↔ a = c - b := by exact Iff.symm eq_sub_iff_add_eq
#check div_eq_iff
#check zero_sub
#check mul_div_right_comm
example (a : ℝ) (h : a ≠ 0) : -a / a = -1 := by exact neg_div_self h
example (a : ℝ) : -1 * a = -a := by exact (neg_eq_neg_one_mul a).symm
#check sub_neg_eq_add
example (a b : ℝ) : (a - b = a + -b) := rfl

-------------------------------------------------------------

#check ContinuousMap.comp
#check Continuous.Prod.mk_left
#check ContinuousMap.prodMk

section

open CategoryTheory

variable {α β : Type} [TopologicalSpace α] [TopologicalSpace β]

example (f : C(α, β)) : TopCat.of α ⟶ TopCat.of β := ↑f

end
