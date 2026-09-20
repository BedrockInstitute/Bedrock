{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import CardinalBridge
import K10.CohenBooleanNamed
import K10.CohenBooleanNotCH
import K10.CohenBooleanOmegaPart
import K10.CohenBooleanPowerTop

module K10.CohenBooleanCHBot
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  (hw : ⟨ CardinalBridge.isOmega 𝒮 w ⟩)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open hPropStructure 𝒮

module Named = K10.CohenBooleanNamed 𝒮 families accessible images pow κ w lem
  using ( powerNm )
module CH = K10.CohenBooleanNotCH 𝒮 families accessible images pow find
  κ w lem hw paths
  using ( module VS ; CH-omega-part ; CH-power-part ; CH-cons ; at2
        ; ⊤B ; ⊥B ; ¬CHsrc ; emptyEnv ; not-CH-from-parts )

booleanPowerNm : CH.VS.Nameᴮ
booleanPowerNm = Named.powerNm

module Omega = K10.CohenBooleanOmegaPart 𝒮 families accessible images pow find
  κ w lem hw paths using ( omega-part-top )
module Power = K10.CohenBooleanPowerTop 𝒮 families accessible images pow
  κ w lem paths using ( power-top )

omega-top : CH.VS.val CH.CH-omega-part (CH.at2 booleanPowerNm) ≡ CH.⊤B
omega-top = Omega.omega-part-top booleanPowerNm

power-top : CH.VS.val CH.CH-power-part (CH.at2 booleanPowerNm) ≡ CH.⊤B
power-top = Power.power-top

module FromParts
  (inner-bot : CH.VS.val CH.CH-cons (CH.at2 booleanPowerNm) ≡ CH.⊥B)
  where

  not-CH-top : CH.VS.val CH.¬CHsrc CH.emptyEnv ≡ CH.⊤B
  not-CH-top = CH.not-CH-from-parts booleanPowerNm omega-top power-top inner-bot
