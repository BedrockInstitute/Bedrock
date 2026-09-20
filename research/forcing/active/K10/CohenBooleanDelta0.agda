{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import K9.BooleanCheckReflection
import K10.CohenValSeam
import K10.CohenBooleanSubst

module K10.CohenBooleanDelta0
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.LevyHierarchy using ( Δ₀ )

module BCR = K9.BooleanCheckReflection 𝒮 families accessible images pow κ w lem
module VS = K10.CohenValSeam 𝒮 families accessible images pow κ w lem paths
module Sub = K10.CohenBooleanSubst 𝒮 families accessible images pow κ w lem paths

module D0 = BCR.Reflection.Delta0
  VS.val
  VS.law-∈ VS.law-≐ VS.law-∧ VS.law-∨ VS.law-⇒ VS.law-⊥
  VS.law-∃∈-ub VS.law-∃∈-lub VS.law-∀∈-lb VS.law-∀∈-glb
  Sub.subst-head

check-Δ₀-val = D0.check-Δ₀
