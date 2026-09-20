{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import K10.CohenBooleanInjKPairFwd

-- Re-export of kpair-sgl-rev from Fwd (one InjSgl instance). Unique cannot
-- co-load with Fwd: two opaque val copies.

module K10.CohenBooleanInjKPairRev
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

module Fwd = K10.CohenBooleanInjKPairFwd 𝒮 families accessible images pow κ w lem paths

kpair-sgl-rev = Fwd.kpair-sgl-rev
sgl-unique = Fwd.sgl-unique
