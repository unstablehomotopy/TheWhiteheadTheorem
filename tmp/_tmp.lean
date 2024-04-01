--@[irreducible]
--def Foo := Nat
-- --example : Foo := (1 : Nat)

-- opaque Foo' : Nat := 1
-- --example : Foo' := (1 : Nat)


import Mathlib.CategoryTheory.Category.Basic

import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.AlgebraicTopology.SimplicialObject
import Mathlib.AlgebraicTopology.SimplexCategory

#check CategoryTheory.SimplicialObject
#check SimplexCategory

#check Functor
-- #check Functor ℕ ℕ

section
  set_option trace.Meta.synthInstance true

  variable {C : Type u} [CategoryTheory.Category.{v} C] {X Y Z : C}
  variable (D : Type u)
  #check C
  #check X
  #check CategoryTheory.Functor C C
  -- #check CategoryTheory.Functor C D
  #check CategoryTheory.Functor ℕ ℝ
  #check CategoryTheory.Functor ℝ ℝ
  #check CategoryTheory.Functor C ℕ
end

section
  variable (C : Type u)
  variable [CategoryTheory.Category.{v} C]
  #check SimplexCategory.skeletalFunctor
  #check CategoryTheory.Functor ℝ ℝ
  #check CategoryTheory.Functor ℕ ℕ
  #check CategoryTheory.Functor C C
  #check CategoryTheory.Functor SimplexCategory SimplexCategory
end

section
  #check CategoryTheory.Category
  variable {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C]
  variable {D : Type u₂} [CategoryTheory.Category.{v₂, u₂} D]
  -- variable {E : Type u} [CategoryTheory.Category.{v} E]
  variable (F : CategoryTheory.Functor C D)
  variable (G : CategoryTheory.Functor C D)
  #check F
  variable (α : CategoryTheory.NatTrans F G)
  #check α
end

----------------------------------------------------

-- Dependent Type Theory
namespace Chapter2 -- limits the scope of definitions and "open"
  section
    def f (n : Nat) : String := toString n
    def g (s : String) : Bool := s.length > 0
    #check fun x => g $ f x

    #check fun (α β γ : Type) (g : β -> γ) (f : α -> β) (x : α) => g $ f x
    def compose (α β γ : Type) (g : β -> γ) (f : α -> β) (x : α)
      : γ := g $ f x

    def pi := 3.14

    #eval let y := 2 + 2; let z := y + y; z * z
  end

  section -- limits the scope of variables, "open", and "set_option"
    variable (α β γ : Type)
    variable (g : β → γ) (f : α → β) (h : α → α)
    variable (x : α)

    def compose' := g (f x)
    def doTwice' := h (h x)
    def doThrice' := h (h (h x))

    #print compose'
    #print doTwice'
    #print doThrice'

    #check List.nil
    #check List.cons
    #check List.map

    #check @List.nil
    #check @List.cons
    #check @List.map
    #check @List.length
    #check @List.append

    -- syntactic gadget
    variable (xs : List Nat)
    #check List.length xs
    #check xs.length

    -- #check List.cons α
    -- #check List.cons Nat
    -- #check List.cons.{1} α
    -- #check List.cons.{1}
    -- #check List.cons.{2}

    #check Π α : Type, List α
    #check (α : Type) -> List α
    #check {α : Type} -> List α
    example : Π α : Type, List α := fun (α : Type) => (List.nil : List α)
    example : Π α : Type, List α := fun (α : Type) => List.nil
    example : Π α : Type, List α := fun _ => List.nil
    example : Π α : Type, List α := @List.nil -- all arguments made explicit by @
    example : (α : Type) -> List α := @List.nil
    example : {α : Type} -> List α := List.nil

    #check Σ α : Type, List α -- dependent Cartesian product
    #check (α : Type) × List α
    example : Σ α : Type, List α := ⟨Nat, [1, 2, 3]⟩
    example : Σ α : Type, List α := Sigma.mk Nat [1, 2, 3]
  end

  #check (2 : Float)
  #check (2 : ℕ)
  #check (2 : ℤ)

  #check Vector
  #check id
  #check Sort 2
  #check Type 2
end Chapter2

-- def compose (α β γ : Type) (g : β -> γ) (f : α -> β) (x : α) : γ := g $ f x

-- Propositions and Proofs
namespace Chapter3
  #check Prop
  #check Sort 0

  #check True
  #check False
  #check And
  #check Implies

  variable (p q r : Prop)
  #check p
  #check And p q -- Prop
  #check Implies p q
  #check p → q


  def conjunction := And p q
  #check conjunction -- Prop → Prop → Prop
  #check fun (p q : Prop) => And p q -- Prop → Prop → Prop

  section
    -- proof irrelevance
    variable (proof1 proof2 : p)
    example : proof1 = proof2 := rfl -- definitionally equal
  end

  theorem or_self : ∀ (b : Bool), or b b = b -- not definitionally equal
    | true => rfl -- notation for "Eq.refl _"
    | false => rfl
  --theorem or_self' : ∀ (b : Bool), or b b = b := rfl
  #check or_self

  theorem t1 : p → q → p := fun (hp : p) (hq : q) => hp
  #print t1
  #check t1

  theorem t1' : p → q → p :=
    fun hp : p =>
    fun hq : q =>
    show p from hp

  theorem t1'' (hp : p) (hq : q) : p := hp

  -- axiom hp : p
  -- theorem t2 : q → p := t1 hp

  #check False.elim -- ex falso sequitur quodlibet (principle of explosion)
  #check absurd
  #check True.intro
  #check And.intro -- only one constructor (hence we can use the anonymous constructor notation)
  #check And.left -- and-elimination
  #check And.right -- and-elimination
  #check Or.intro_left
  #check Or.intro_right
  #check Or.inr
  #check Or.inl
  #check Or.elim
  #check Iff.intro
  #check Iff.mp
  #check Iff.mpr

  section
    variable (hp : p) (hq : q) (hr : r)
    #check And.intro hp hq
    #check (⟨hp, hq⟩ : p ∧ q)
    #check (⟨hp, hq, hr⟩ : p ∧ q ∧ r)
    #check (⟨hp, ⟨hq, hr⟩⟩ : p ∧ q ∧ r)
    -- #check (⟨⟨hp, hq⟩, hr⟩ : p ∧ q ∧ r) -- error
  end

  example (h : p ∧ q) : q ∧ p := ⟨And.right h, And.left h⟩
  example (h : p ∧ q) : q ∧ p := ⟨h.right, h.left⟩ -- syntactic gadget

  -- introducing auxiliary subgoals
  example (h : p ∧ q) : q ∧ p :=
    have hp : p := h.left
    have hq : q := h.right
    show q ∧ p from And.intro hq hp

  example (h : p ∧ q) : q ∧ p :=
    have hp : p := h.left
    suffices hq : q from And.intro hq hp
    show q from And.right h

  -- example (h : p ∧ q) : q ∧ p :=
  --   have hp : p := h.left
  --   suffices hq : q from _
  --   show q from _

  --open Classical -- clssical logic (assuming law of excluded middle)
  -- already opened by something in mathlib.Logic.Basic
  #check em
  -- double negation elimination
  theorem dne {p : Prop} (h : ¬¬p) : p :=
    Or.elim (em p)
      (fun hp : p => hp)
      (fun hnp : ¬p => absurd hnp h)
  example (h : ¬¬p) : p :=
    Classical.byCases
      (fun h1 : p => h1)
      (fun h1 : ¬p => absurd h1 h)
  example (h : ¬¬p) : p :=
    Classical.byContradiction
      (fun h1 : ¬p =>
      show False from h h1)
end Chapter3

-- Quantifiers and Equality
namespace Chapter4
  variable (α : Type) (r : α → α → Prop)

  variable (refl_r : ∀ x, r x x)
  variable (symm_r : ∀ {x y}, r x y → r y x)
  variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

  example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
    trans_r (trans_r hab (symm_r hcb)) hcd

  -- "Prop" is impredicative (?)


  #check Eq
  #check Eq.refl
  #check Eq.symm
  #check Eq.trans
  #check Eq.subst -- ∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a → motive b

  universe u
  #check @Eq.refl.{u}
  #check @Eq.symm.{u}
  #check @Eq.trans.{u}

  example (α : Type) (a b : α) (p : α → Prop)
      (h1 : a = b) (h2 : p a) : p b :=
    h1 ▸ h2 -- similar to Eq.subst h1 h2,
    -- but ▸ uses more effective heuristics to search for {motive : α → Prop}

  #check congrArg
  #check congrFun
  #check congr


  def divides (x y : Nat) : Prop :=
    ∃ k, k*x = y

  def divides_trans (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
    let ⟨k₁, d₁⟩ := h₁
    let ⟨k₂, d₂⟩ := h₂
    ⟨k₁ * k₂, by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]⟩

  def divides_mul (x : Nat) (k : Nat) : divides x (k*x) :=
    ⟨k, rfl⟩

  instance : Trans divides divides divides where
    trans := divides_trans

  example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
    calc
      divides x y     := h₁
      _ = z           := h₂
      divides _ (2*z) := divides_mul ..

  infix:50 " || " => divides

  example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
    calc
      x || y   := h₁
      _ = z    := h₂
      _ || 2*z := divides_mul ..

end Chapter4


namespace Chapter7

  inductive Weekday where
 | sunday : Weekday
 | monday : Weekday
 | tuesday : Weekday
 | wednesday : Weekday
 | thursday : Weekday
 | friday : Weekday
 | saturday : Weekday
 deriving Repr

  namespace Weekday
    def next (d : Weekday) : Weekday :=
      match d with
      | sunday    => monday
      | monday    => tuesday
      | tuesday   => wednesday
      | wednesday => thursday
      | thursday  => friday
      | friday    => saturday
      | saturday  => sunday

    def previous (d : Weekday) : Weekday :=
      match d with
      | sunday    => saturday
      | monday    => sunday
      | tuesday   => monday
      | wednesday => tuesday
      | thursday  => wednesday
      | friday    => thursday
      | saturday  => friday

    #eval next (next tuesday)      -- Weekday.thursday
    #eval next (previous tuesday)  -- Weekday.tuesday

    example : next (previous tuesday) = tuesday :=
      rfl

    def next_previous (d : Weekday) : next (previous d) = d := by
      cases d <;> rfl
  end Weekday

end Chapter7
