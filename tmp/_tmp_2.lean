-- reference:
-- https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/quasicategories

import Mathlib.CategoryTheory.Category.Basic

import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.AlgebraicTopology.SimplicialObject

namespace InfCategory
  open CategoryTheory
  open Simplicial -- notations such as `Λ[n, i]` and `Δ[n]` become available

  section
    universe v₁ v₂ v₃ u₁ u₂ u₃
    open NatTrans Category CategoryTheory.Functor
    variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]
    #check C
  end

  section
    variable (x : ℤ)
    #check (x : ℕ)
  end

  section
    def takeWhile (p : α → Bool) (as : Array α) : Array α :=
      go 0 #[]
    where
      go (i : Nat) (r : Array α) : Array α :=
        if h : i < as.size then
          let a := as.get ⟨i, h⟩
          if p a then
            go (i+1) (r.push a)
          else
            r
        else
          r
    termination_by go i r => as.size - i

    #print Array
  end

  section
    variable (X Y : SSet)
    set_option trace.Meta.synthInstance true
    #print Category
    #print SimplicialObject
    #check (inferInstance : Category SSet)
    #check (inferInstance : CategoryTheory.Functor X) -- ?
    #check X ⟶ Y
    #check NatTrans X Y

    def NatGtZero := {X : Nat // X > 0}
    #check NatGtZero
    example : NatGtZero := ⟨1, by decide⟩
    section
      variable (n : NatGtZero)
      #check n.val
      #check n.property
      #check n.1
      #check n.2
    end

    instance : ToString NatGtZero where
      toString p := toString p.1

    #check (inferInstance : ToString Nat)
    #check (inferInstance : ToString NatGtZero)

    def Vec (n : Nat) (a : Type) := { ls : List a // ls.length = n }
    example : Vec 3 Nat := ⟨[1, 2, 3], rfl⟩
  end

  def horn_filling_condition (X : SSet) (n i : Nat): Prop :=
    ∀ f : Λ[n, i] ⟶ X, ∃ g : Δ[n] ⟶ X,
    f = SSet.hornInclusion n i ≫ g

  -- def inner_horn_filling_condition (X : SSet) : Prop :=
  --   ∀ (n i : Nat), n ≥ 2 ∧ 0 < i ∧ i < n →
  --   ∀ f : Λ[n, i] ⟶ X, ∃ g : Δ[n] ⟶ X,
  --   f = SSet.hornInclusion n i ≫ g

  /-- A simplicial set is called an ∞-category if it has the extension property
  for all inner horn inclusions `Λ[n, i] ⟶ Δ[n]`, n ≥ 2, 0 < i < n. -/
  def InfCategory := {X : SSet //
    ∀ (n i : Nat), n ≥ 2 ∧ 0 < i ∧ i < n → horn_filling_condition X n i}

  /-- A Kan complex is a simplicial set X which has the extension property
  for horn inclusions `Λ[n, i] ⟶ Δ[n]` for 0 ≤ i ≤ n. -/
  def KanComplex := {X : SSet //
    ∀ (n i : Nat), 0 ≤ i ∧ i ≤ n → horn_filling_condition X n i}

  #check (inferInstance : Category SSet)
  -- #check (inferInstance : Category InfCategory)
  -- instance : Category InfCategory := inferInstance -- ?
  -- instance : Category InfCategory := by -- ?
  --   dsimp only [InfCategory]
  --   infer_instance
  instance : Category InfCategory where -- reference: https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Functor/Category.html
    Hom X Y := NatTrans X.1 Y.1
    id X := NatTrans.id X.1
    comp α β := NatTrans.vcomp α β
  instance : Category KanComplex where
    Hom X Y := NatTrans X.1 Y.1
    id X := NatTrans.id X.1
    comp α β := NatTrans.vcomp α β
  #check (inferInstance : Category InfCategory)
  #check (inferInstance : Category KanComplex)

end InfCategory

----------------------------------

namespace SSet
  #check horn
  #check hornInclusion

  #check CategoryTheory.Functor.prod

  open CategoryTheory
  open Simplicial

  /- The product of two simplicial sets -/
  def prod (X : SSet.{u}) (Y : SSet.{v}) : SSet.{max u v} where
    obj n := (X.obj n) × (Y.obj n)
    map {n₁ n₂} f α := ⟨X.map f α.1, Y.map f α.2⟩
    -- map {n₁ n₂} f α := {
    --   fst := X.map f α.1
    --   snd := Y.map f α.2
    -- }

  /- The internal hom -/
  def hom (X : SSet.{u}) (Y : SSet.{u}) : SSet.{_} where
    obj n := NatTrans (prod X (standardSimplex.obj (Opposite.unop n))) Y

  section
    variable (X : SSet.{u}) (Y : SSet.{v})
    #check prod X Y
    variable (n_nat : ℕ)
    variable (m : SimplixCategroyᵒᵖ)
    def n := SimplexCategory.mk n_nat
    open Simplicial
    #check X _[0] -- notation defined in SimplicialObject.lean
    #check n
    #check Opposite.op m
    #check Opposite.unop m
    #check m.unop
  end

  #check Opposite.op
  #check Opposite.unop

end SSet


#check SSet
#check CategoryTheory.SimplicialObject
