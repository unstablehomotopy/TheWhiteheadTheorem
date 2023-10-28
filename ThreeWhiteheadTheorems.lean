/- IMPORTS -/

import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Types 
import Mathlib.CategoryTheory.DiscreteCategory
import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.CategoryTheory.Category.Init
--import Mathlib.CategoryTheory.Monad.Algebra
import Aesop
import Init
import Mathlib.CategoryTheory.DiscreteCategory
import Mathlib.CategoryTheory.Bicategory.Strict
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.CategoryTheory.Functor.Basic
import Init.Core
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monad.Algebra
import Mathlib.CategoryTheory.Monad.Monadicity
import Mathlib.CategoryTheory.Monad.Basic
universe u
universe v

import Mathlib.AlgebraicTopology.SimplexCategory
import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.AlgebraicTopology.TopologicalSimplex -- auxiliary definitions for AlgebraicTopology.SimplicialSet
import Mathlib.Topology.Homotopy.HomotopyGroup      -- Cube
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category      -- category of functors
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Bicategory.IsKan
import Mathlib.CategoryTheory.Bicategory.Extension




/- CHAPTER 1 -/



open CategoryTheory


#check CategoryTheory.Bicategory.mk
#check CategoryTheory.Bicategory.Strict
#check CategoryTheory.Bicategory.Strict.mk
#check CategoryTheory.Functor
#check CategoryTheory.Functor.mk
#check CategoryTheory.CategoryStruct


def zero : Nat := 0


def reflexivity {X : Type} {x : X} : x = x := Eq.refl x


def symmetry {X : Type} {x : X} {y : X}  (p : x = y) := Eq.symm p


def transitivity {X : Type} {x : X} {y : X} {z : X} (p : x = y) (q : y = z) := Eq.trans p q


def extensionality (f g : X → Y) (p : (x:X) → f x = g x) : f = g := funext p


def equal_arguments {X : Type} {Y : Type} {a : X} {b : X} (f : X → Y) (p : a = b) : f a = f b := congrArg f p

def equal_functions {X : Type} {Y : Type} {f₁ : X → Y} {f₂ : X → Y} (p : f₁ = f₂) (x : X) : f₁ x = f₂ x := congrFun p x

def pairwise {A : Type} {B : Type} (a₁ : A) (a₂ : A) (b₁ : B) (b₂ : B) (p : a₁ = a₂) (q : b₁ = b₂) : (a₁,b₁)=(a₂,b₂) := (congr ((congrArg Prod.mk) p) q)


def ℂ𝕒𝕥 : (CategoryTheory.Bicategory CategoryTheory.Cat) := CategoryTheory.Cat.bicategory

#check ℂ𝕒𝕥

variable {C : Cat}
#check C.α
#check C.str
#check C.str.Hom


#check ℂ𝕒𝕥


#check ℂ𝕒𝕥
#check ℂ𝕒𝕥.Hom
#check ℂ𝕒𝕥.id
#check ℂ𝕒𝕥.comp
#check ℂ𝕒𝕥.whiskerLeft
notation F "◁" η => ℂ𝕒𝕥.whiskerLeft F η
#check ℂ𝕒𝕥.whiskerRight
notation η "▷" F => ℂ𝕒𝕥.whiskerRight η F
#check ℂ𝕒𝕥.associator
#check ℂ𝕒𝕥.leftUnitor
#check ℂ𝕒𝕥.rightUnitor
#check ℂ𝕒𝕥.whiskerLeft_id
#check ℂ𝕒𝕥.whiskerLeft_comp
#check ℂ𝕒𝕥.id_whiskerLeft 
#check ℂ𝕒𝕥.comp_whiskerLeft
#check ℂ𝕒𝕥.id_whiskerRight
#check ℂ𝕒𝕥.comp_whiskerRight
#check ℂ𝕒𝕥.whiskerRight_comp
#check ℂ𝕒𝕥.whiskerRight_id 
#check ℂ𝕒𝕥.whisker_assoc
#check ℂ𝕒𝕥.whisker_exchange
#check ℂ𝕒𝕥.pentagon
#check ℂ𝕒𝕥.triangle




variable {C : Cat}
variable {D : Cat}
variable {Φ  :C ≅ D }
#check Φ.hom
#check Φ.inv
#check Φ.hom_inv_id
#check Φ.inv_hom_id


notation A "•" B => B ≫ A
notation A "⭢" B => A ⟶ B


-----------------------------------------
-- simplicial sets
-----------------------------------------

#check SSet
-- SSet.{u} : Type (u + 1)

#check SSet.standardSimplex
-- SSet.standardSimplex : CategoryTheory.Functor SimplexCategory SSet

#check SSet.boundary
-- SSet.boundary (n : ℕ) : SSet

#check SSet.boundaryInclusion
-- SSet.boundaryInclusion (n : ℕ) :
--   SSet.boundary n ⟶ SSet.standardSimplex.obj (SimplexCategory.mk n)

#check SSet.horn
-- SSet.horn (n : ℕ) (i : Fin (n + 1)) : SSet

#check SSet.hornInclusion
-- SSet.hornInclusion (n : ℕ) (i : Fin (n + 1)) :
--   SSet.horn n i ⟶ SSet.standardSimplex.obj (SimplexCategory.mk n)

#check Cube.boundary
-- Cube.boundary.{u_1} (N : Type u_1) : Set (N → ↑unitInterval)
--   -- ↑ means type coersion, which can often be omitted

-----------------------------------------
-- category theory
-----------------------------------------

#check CategoryTheory.Category
-- CategoryTheory.Category.{v, u} (obj : Type u) : Type (max u (v + 1))

#check CategoryTheory.Functor
-- CategoryTheory.Functor.{v₁, v₂, u₁, u₂}
--   (C : Type u₁) [inst✝ : CategoryTheory.Category.{v₁, u₁} C]
--   (D : Type u₂) [inst✝¹ : CategoryTheory.Category.{v₂, u₂} D] :
--      Type (max v₁ v₂ u₁ u₂)

#check CategoryTheory.Functor.category -- category of functors
-- CategoryTheory.Functor.category.{v₁, v₂, u₁, u₂}
--   {C : Type u₁} [inst✝ : CategoryTheory.Category.{v₁, u₁} C]
--   {D : Type u₂} [inst✝¹ : CategoryTheory.Category.{v₂, u₂} D] :
--      CategoryTheory.Category.{max u₁ v₂, max (max (max u₂ u₁) v₂) v₁}
--        (CategoryTheory.Functor C D)

#check CategoryTheory.yoneda
-- CategoryTheory.yoneda.{v₁, u₁}
--   {C : Type u₁} [inst✝ : CategoryTheory.Category.{v₁, u₁} C] :
--     CategoryTheory.Functor C (CategoryTheory.Functor Cᵒᵖ (Type v₁))

#check CategoryTheory.coyoneda
-- CategoryTheory.coyoneda.{v₁, u₁}
--   {C : Type u₁} [inst✝ : CategoryTheory.Category.{v₁, u₁} C] :
--     CategoryTheory.Functor Cᵒᵖ (CategoryTheory.Functor C (Type v₁))

-----------------------------------------
-- bicategories
-----------------------------------------

#check CategoryTheory.Bicategory
-- CategoryTheory.Bicategory.{w, v, u} (B : Type u) : Type (max (max u (v + 1)) (w + 1))

#check CategoryTheory.Bicategory.LeftExtension.IsKan
-- CategoryTheory.Bicategory.LeftExtension.IsKan.{w, v, u}
--   {B : Type u} [inst✝ : CategoryTheory.Bicategory B] {a b c : B} {f : a ⟶ b} {g : a ⟶ c}
--   (t : CategoryTheory.Bicategory.LeftExtension f g) : Type (max (max v w) w)
-- `IsKan t` is a structure containing the data of 2-morphisms which ensure
-- that `t` is a Kan extension.


#check CategoryTheory.Bicategory.LeftExtension
-- CategoryTheory.Bicategory.LeftExtension.{w, v, u}
--   {B : Type u} [inst✝ : CategoryTheory.Bicategory B] {a b c : B}
--   (f : a ⟶ b) (g : a ⟶ c) : Type (max v w)




-- PART I: ∞-Categories

/- CHAPTER 2 -/


/- CHAPTER 3 -/


/- CHAPTER 4 -/


/- CHAPTER 5 -/


/- CHAPTER 6 -/


-- PART II: ∞-GROUPOIDS

/- CHAPTER 7 -/


/- CHAPTER 8 -/


/- CHAPTER 9 -/


/- CHAPTER 10 -/


/- CHAPTER 11 -/


-- PART III: Based Connected ∞-Groupoids

/- CHAPTER 12 -/


/- CHAPTER 13 -/


/- CHAPTER 14 -/


/- CHAPTER 15 -/


/- CHAPTER 16 -/