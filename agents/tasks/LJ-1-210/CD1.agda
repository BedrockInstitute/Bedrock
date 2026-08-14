{-# OPTIONS --cubical --safe --guardedness #-}
open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( Transitive )
open import V.Hierarchy using ( 𝒮ᵥ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
module LJ-1-210.CD1 where
record ClassData (ℓ : Level) : Type (ℓ-suc (ℓ-suc ℓ)) where
  field
    M : V ℓ → hProp (ℓ-suc ℓ)
    M-trans : Transitive (𝒮ᵥ {ℓ}) M
