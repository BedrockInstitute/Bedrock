{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import K10.CohenBooleanCheckMem
import K10.CohenBooleanInjBot

module K10.CohenBooleanInjMem
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
open import FOL.Syntax using ( var ; _∈̇_ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module IB = K10.CohenBooleanInjBot 𝒮 families accessible images pow κ w lem paths
module Mem = K10.CohenBooleanCheckMem 𝒮 families accessible images pow κ w lem

open IB using ( Src ; emptyEnv ; checkNm ; val ; law-∈ ; ⊤B )

memSrc : Src 2
memSrc = var zero ∈̇ var (suc zero)

check-mem-top : (a b : S) → ⟨ a ∈ˢ b ⟩
  → val memSrc (checkNm a ∷ checkNm b ∷ emptyEnv) ≡ ⊤B
check-mem-top a b h =
  law-∈ zero (suc zero) (checkNm a ∷ checkNm b ∷ emptyEnv)
  ∙ Mem.check-∈-top a b h

module AtCardinal (ω₁ : S) (hw₁ : ⟨ w ∈ˢ ω₁ ⟩) where

  omega-in-top : val memSrc (checkNm w ∷ checkNm ω₁ ∷ emptyEnv) ≡ ⊤B
  omega-in-top = check-mem-top w ω₁ hw₁
