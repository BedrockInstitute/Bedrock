{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import K6.NameBuildAtGround
import K9.NameGround

module K10.CohenBooleanCands
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module NG = K9.NameGround 𝒮 families accessible images pow κ w
module NB = K6.NameBuildAtGround.Seam 𝒮 families accessible NG.C.carrier

cands : S
cands = NB.Valid.candidates NG.hasSeparation pow (NG.Check.chk w)

cands-name : (σ : S) → ⟨ σ ∈ˢ cands ⟩ → ⟨ NG.K.IsName σ ⟩
cands-name = NB.Valid.candidates-name NG.hasSeparation pow (NG.Check.chk w)
