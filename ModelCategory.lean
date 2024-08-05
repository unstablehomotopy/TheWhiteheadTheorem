-- import LeanCopilot

import Mathlib.CategoryTheory.Square
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
import Mathlib.CategoryTheory.MorphismProperty.Factorization
import Mathlib.CategoryTheory.SmallObject.Construction

-----------------------------------------------------------------

-- example (a b c : Nat) : a + b + c = a + c + b := by
--   suggest_tactics "rw"

open CategoryTheory

#check MorphismProperty
#check MorphismProperty.MapFactorizationData
#check MorphismProperty.FactorizationData


section LiftingProperties

#check CommSq.HasLift
#check HasLiftingProperty
#check Square               -- import Mathlib.CategoryTheory.Square
#check Square.isPushout_iff -- import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
#check IsPullback           -- import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq


variable {C : Type*} [Category C] {A B A' B' X Y : C}
  (a : A ⟶ A') (i : A ⟶ B) (i' : A' ⟶ B') (b : B ⟶ B') (f : X ⟶ Y)

/--
```
  A ---a---> A' ---s--> X
  |          |          |
  i          i'         f
  |    p.o.  |          |
  v          v          v
  B ---b---> B' ---t--> Y

```
-/
lemma pushout_preserves_left_lifting_property
    (h : HasLiftingProperty i f) (po : IsPushout a i i' b) : HasLiftingProperty i' f :=
  ⟨fun {s} {t} sq => by
    have big_sq := CommSq.horiz_comp ⟨po.w⟩ sq
    have big_sq_hasLift := h.sq_hasLift big_sq
    have g := big_sq_hasLift.exists_lift.some
    have sq_lift : sq.LiftStruct := {
      l := po.desc s g.l g.fac_left.symm
      fac_left := IsPushout.inl_desc po s g.l g.fac_left.symm
      fac_right := sorry
    }
    exact ⟨Nonempty.intro sq_lift⟩⟩

end LiftingProperties

-- small object argument
#check SmallObject.functor
