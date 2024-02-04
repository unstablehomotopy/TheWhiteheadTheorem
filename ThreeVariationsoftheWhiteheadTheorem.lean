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

universe u
universe v
/-
I've written out some of the more immediate tasks on our agenda.

The first goal (Whitehead theorem (a)
appears to be two to four months away.
Here I've written some tasks. The idea
is that we would have a more
concrete list of items to go through,
and that for each one we would either
complete the task, break it down into smaller ones
(which is almost always helpful),
add some #check's, pass the task on to the other,
or ask for more of a breakdown.
I was thinking the way we'd do this is like this:
I'll type your initials --JX next to the one I
want you to look at. Then if it's too much or
you're confused then replace it with --DY and
I'll take the message to break it down further

-/

/-
A smaller goal could be creating the following derived categories, along with properties of geometric realization:

* ∞-Cat
* ∞-Cat⁄C
* D(∞-Cat)
* D(∞-Cat⁄C)
* ∞-Grpd
* ∞-Grpd⁄G
* D(∞-Grpd)
* D(∞-Grpd₀)
* D(∞-Grpd₀/G)
* D(∞-Grpd₀)
* D(∞-Grpd₀/G₀)
-/

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
/-
I'm wondering exactly what kind of cube this is...
is it (Δ¹)ⁿ, or (γ)ⁿ for some γ with b
-/


-- JX
/-
Let's see what  definition of the internal hom of simplicial sets...
specifically starting with [Δ¹, X]
-/

/-
definition of [Δ¹, X] **as a simplicial set**

https://ncatlab.org/nlab/show/internal+hom#in_simplicial_sets
(see "In Simplicial Sets")
-/

/-
the basic idea is that the set of n-simplices is defined like so:

SSetHom X Y n := Hom_(Set) (X × Δ[n], Y)
SSetHom X Y face...
SSetHom X Y degeneracy...
-/

/-
the main use of this for us (and potentially even the only one?)
is in defining the six homotopical operations on the front cover.
We'll need [Δ¹,-] for this... but also the functorial one...
so we need to defien SSetHom on MAPS as well...
see if you can write out more of the components possibly with some sorries
(the components of the SSetHom in the above)... then we can add in the definition for maps
-/

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

#check CategoryTheory.NatTrans

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



/-
perhaps something for the maps...
-/

-- note that (X : C) is really (X : C.α), and that C.α is what we write for
-- the object component of a category


/-
def horn_filling (X : SSet) : ∀(n : ℕ),∀(i : Fin (n + 1)),∀
-/

--
/-
def inner horn filling condition should feature 0 < i and either i < n +1 or i < n (I can't tell which)
-/



/-
- Definition of ∞-Cat.α (the type of quasicategories with inner horn filling condition)
-/

/-
the definition of ∞-Cat.str is not that hard, since
∞-Cat is a fully faithful subcategory of the category
of simplicial sets.
-/

-- in what follows we'd like to define all of the components of the InfCatstr (everything that isn't the object component)

-- ⥤

notation C "-->" D => C ⥤ D
notation F "--->" G => CategoryTheory.NatTrans F G
notation η "---->" ε => CategoryTheory.NatTrans.ext η ε

#check CategoryTheory.NatTrans.ext

-- def InfCatstrHom
-- def InfCatstr???
-- def InfCatstr???
-- def InfCatstr???
-- def InfCatstr

variable (f : SSet → Prop)

#check SSet.standardSimplex
-- SSet.standardSimplex : CategoryTheory.Functor SimplexCategory SSet

#check SSet.horn
-- SSet.horn (n : ℕ) (i : Fin (n + 1)) : SSet

#check Unit

#check SSet
variable (X : SSet)
variable (Y : SSet)
#check X ⭢ Y

#check SSet.hornInclusion
-- SSet.hornInclusion (n : ℕ) (i : Fin (n + 1)) :
--   SSet.horn n i ⟶ SSet.standardSimplex.obj (SimplexCategory.mk n)

-- #check Fin n

-- D()
-- D()
-- D()
-- #check 0 < 1



def make_an_element_of_Fin (n : Nat) (N : Nat) (p : 0 < n) (q : n < N) : Fin N := by sorry
-- def FintoNat (N : Nat) (f : Fin n) : Nat := f.val
-- def FintoGeq (N : Nat) (f : Fin n) : 0 < (FintoNat N f) :=
-- def FintoLeq (N : Nat) (f : Fin n) : (FintoNat N f) <= N :=
-- def  { a :=  , b :=  }

-- def inner_horn_filling_condition ()

-- SSet.standardSimplex.obj
--
--

variable (T : Type)
variable (S : Type)

-- ≫
-- ≫
-- :---> :---> ⥤ ⟶ :---> ⭢
--

variable (n : Nat)
#check (SimplexCategory.mk n)
-- SSet.horn

variable {n : Nat}
notation "Δⁿ" =>  SSet.standardSimplex.obj (SimplexCategory.mk n)
#check Δⁿ

-- Inner horn filling condition

def inner_horn_filling_condition (X : SSet) : Prop := ∀(f : SSet.horn X),∀(N : Nat),∃(g : (SSet.standardSimplex.obj (SimplexCategory.mk n)) ⭢ X),SSet.hornInclusion g


-- Horn filling condition
def horn_filling_condition (X : SSet) : Prop := by sorry


-- Type should instead be something more sophisticated
def quasicategory : Type (u+1) := { X : SSet // inner_horn_filling_condition X}
/-
recall the the three fundamentals of restricted comprehension:

-/

def Kan_complex : Type (u+1) := { X : SSet // horn_filling_condition X}
/-
Considerations and future changes: we may prefer to
replace this with a different construction of the same set,
but I see no reason to for now.
-/



def InfCat : Category quasicategory := sorry

notation "∞-Cat" => InfCat


-- def homotopy (X : ∞-Cat) (Y : ∞-Cat) (f : X ⭢ Y) (g : X ⭢ Y) :  := by sorry
/-

-/

/-
next comes the derived category....

we're basically going to make two of these, and I'm pretty sure we need both...

the easier one is constructed using the same objects as ∞-Cat and has as its morphisms equivalence classes
of morphisms ...

all in all we'd like to write out all of the entries with some sorries (like seven of them)
-/

def DerInfCat : Cat := sorry




-- Definition of Ω⃗, i.e. [Δ¹, -]
/-
Here we will define a functor Ω⃗ : Functor ∞-Cat ∞-Cat
note to self: it's super unfortunate that these
combining unicode over characters don't always work.
Maybe we can find some other sort of notation which does.
Searching through the unicode catalogue can be fun
https://en.wikipedia.org/wiki/Unicode_subscripts_and_superscripts
-/

def directed_path_space : Functor ∞-Cat ∞-Cat := sorry

-- Our next goal will mainly be to define
/-

-/

notation "Ω⃗" => directed_path_space

/-
check their Ovr
-/

/-
After that we'll define D(∞-Cat/C)
-/

def DerInfCatOvr (C : ∞-Cat) : Cat := sorry


/-

-/

-- next we'll define π⃗ₙ
/-
- Definition of π⃗ₙ using Ω⃗
-/

#check ∞-Cat
#check Type ⥤ Type
def pi (n : Nat) : Functor (∞-Cat) Type := by sorry
notation "π" n => pi n


/-

-/



/- CHAPTER 2 -/

/-
In Lurie's HTT, which uses Joyal's theory of quasicategories, three model structures are established,
or really two, one of which comes in left and right forms. Details on these model structures are available
at:

https://people.math.harvard.edu/~lurie/papers/highertopoi.pdf

terminology (xiv)


See also:
- Proposition 1.2.5.1 due to Joyal
- Definition 2.0.0.3 (page 53) due to Joyal
- Available here: https://www.sciencedirect.com/science/article/pii/S0022404902001354

-/

/-
Mathlib's SSet.
-/

#check SSet.S1
#check SSet.toTop
#check SSet.sk
#check SSet.Truncated
#check SSet.hom_ext
#check CategoryTheory.Cat SSet
#check SSet.asOrderHom
#check SSet.hornInclusion



/-
in the last section we have defined
we'll have moved the insights on
simplicial sets to the beginning
-/

-- REP (the replacement functor)

def REP : Functor ∞-Cat ∞-Cat := sorry

def REPn (n : Nat) : Functor ∞-Cat ∞-Cat := sorry


/-
def REPnobj

def REPnhom
-/


-- HEP (the directed homotopy extension theorem)



/- CHAPTER 3 -/


/- CHAPTER 4 -/


/- CHAPTER 5 -/


/- CHAPTER 6 -/


-- PART II: ∞-GROUPOIDS

/- CHAPTER 7 -/

/-
We construct our category of infinity groupoids from objects in SSet with the Kan filling conditiion

-/


notation "∞-Grpd" => InfGrpd

-- notation "D⃡(∞-Grpd)" => DerInfGrpd
/-
The symbol D⃡ can be compared with the symbol π⃡₀,
even though former is just notation
-/

-- over category of ∞-Grpd ⁄ G

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
