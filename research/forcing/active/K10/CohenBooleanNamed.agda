{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import K9.BooleanNameGround
import K10.CohenBooleanCands
import K10.CohenBooleanSubset
import K10.CohenBooleanPower
import K10.CohenNameIntro

module K10.CohenBooleanNamed
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module Cands = K10.CohenBooleanCands 𝒮 families accessible images pow κ w
module Sub = K10.CohenBooleanSubset 𝒮 families accessible images pow κ w lem
module Power = K10.CohenBooleanPower 𝒮 families accessible images pow κ w lem
module NI = K10.CohenNameIntro 𝒮 families accessible images pow κ w lem
module BNG = K9.BooleanNameGround 𝒮 families accessible images pow κ w lem
open BNG using ( module BK ; module Translation )

entry-data : NI.EntryData Cands.cands Sub.candEntry
entry-data σ hσ =
  Translation.trᴮ σ
  , Sub.candWeight σ
  , Sub.candEntry-weight σ
  , Sub.candWeight-inB σ
  , Translation.trᴮ-name σ (Cands.cands-name σ hσ)

listing : NI.Listing Power.powerB
listing = NI.mkListing Power.powerB Cands.cands Sub.candEntry
  Power.powerB-spec entry-data

powerNm : Σ[ x ∈ S ] ⟨ BK.IsName x ⟩
powerNm = Power.powerB , NI.mkName Power.powerB listing
