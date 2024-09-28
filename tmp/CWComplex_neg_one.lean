/-
The definition of CW complexes follows David Wärn's suggestion at
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Do.20we.20have.20CW.20complexes.3F/near/231769080
-/

import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Analysis.InnerProductSpace.PiL2

open CategoryTheory

namespace CWComplex

noncomputable def sphere (n : {n : ℤ // n ≥ -1}) : TopCat :=
  if n.val = -1 then TopCat.of Empty
  else TopCat.of <| Metric.sphere (0 : EuclideanSpace ℝ <| Fin <| Int.toNat <| n + 1) 1

noncomputable def closedBall (n : ℕ) : TopCat :=
  TopCat.of <| Metric.closedBall (0 : EuclideanSpace ℝ <| Fin n) 1

notation "𝕊 "n => sphere n
notation "𝔻 "n => closedBall n

def sphereInclusion (n : {n : ℤ // n ≥ -1}) : (𝕊 n) → (𝔻 Int.toNat n + 1) :=
  if h : n.val = -1 then by
    rw [sphere, h]
    exact Empty.rec
  else by
    rw [sphere]
    simp only [h, reduceIte]
    exact fun ⟨pt, hpt⟩ => ⟨pt, le_of_eq hpt⟩

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
