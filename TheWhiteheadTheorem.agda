{-# OPTIONS --cubical #-}

-- Example.agda
module TheWhiteheadTheorem where

-- Import the natural number module from the standard library
open import Data.Nat
open import Cubical.Cohomology.Base

--For the braid group
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Free --For presentations
open import Cubical.Algebra.Group.IsomorphismTheorems
open import Cubical.Algebra.Group.Morphisms --For presentations
open import Cubical.Algebra.Group.QuotientGroup
open import Cubical.Algebra.CommMonoid


--open import Cubical.Algebra.AbGroup
--oepn import Cubical.Algebra.

open import Cubical.HITs.Sn

-- Define a function to add two numbers
add : ℕ → ℕ → ℕ
add m n = m + n

--Presenting the braid-group
        