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
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Analysis.InnerProductSpace.PiL2 -- EuclideanSpace
import Mathlib.Init.Set

open CategoryTheory


namespace CWComplex
noncomputable section

def Sphere : ℤ → TopCat
  | Int.ofNat n => TopCat.of <| Metric.sphere (0 : EuclideanSpace ℝ <| Fin <| n + 1) 1
  | _           => TopCat.of Empty

def ClosedBall : ℤ → TopCat
  | Int.ofNat n => TopCat.of <| Metric.closedBall (0 : EuclideanSpace ℝ <| Fin n) 1
  | _           => TopCat.of Empty

notation:0 "𝕊 "n => Sphere n
notation:0 "𝔻 "n => ClosedBall n

def SphereInclusion (n : ℤ) : (𝕊 n) → (𝔻 n + 1) :=
  match n with
  | Int.ofNat _   => fun ⟨pt, hpt⟩ => ⟨pt, le_of_eq hpt⟩
  | Int.negSucc _ => Empty.rec

theorem continuous_SphereInclusion (n : ℤ) : Continuous (SphereInclusion n) :=
  match n with
  | Int.ofNat _ => ⟨by
      intro _ ⟨t, ht, ht'⟩
      rw [isOpen_induced_iff]
      use t, ht
      rw [ht'.symm]
      tauto⟩
  | Int.negSucc n => ⟨by
      dsimp [SphereInclusion, ClosedBall]
      intro s hs
      sorry⟩

end
end CWComplex
