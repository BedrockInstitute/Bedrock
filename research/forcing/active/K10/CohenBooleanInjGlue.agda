{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import K10.CohenBooleanInjForce
import K10.CohenBooleanInjMaps

-- Smoke: compiled injBody and the memAtˢ hit Formula in one module.
-- No CCC. No CheckMem. Unique/total remain parameters of InjSelect.

module K10.CohenBooleanInjGlue
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

open import FOL.ZFStructure using ( module hPropStructure )
open hPropStructure 𝒮

module Force = K10.CohenBooleanInjForce 𝒮 families accessible images pow κ w lem paths
module Maps = K10.CohenBooleanInjMaps 𝒮 families accessible images pow κ w lem paths

open Force using ( val ; injBody ; checkNm ; emptyEnv ; i ; Cond ; Nameᴮ )
open Maps using ( hitFo )

hit-at : Nameᴮ → Cond → S → _
hit-at σ p ω₁ = hitFo (fst σ) (fst p) ω₁

forced-body : Nameᴮ → S → _
forced-body σ ω₁ = val injBody (σ ∷ checkNm ω₁ ∷ checkNm w ∷ emptyEnv)
