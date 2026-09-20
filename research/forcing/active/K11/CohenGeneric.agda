{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import CodedCompletion
import K9.NameGround
import K8.Cohen
import K11.CountableCohen

module K11.CohenGeneric
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open hPropStructure 𝒮

module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( extensional ; ≈ˢ-paths ; hasSeparation ; hasPair ; hasUnion )
module C = K8.Cohen 𝒮 NG.extensional NG.≈ˢ-paths NG.hasPair NG.hasUnion pow NG.hasSeparation κ w
  using ( presentation ; laws ; module GS ; module PM )
module K = CodedCompletion.Core 𝒮 NG.extensional pow NG.hasSeparation NG.≈ˢ-paths
  C.presentation C.laws
module FS = K.FS
open FS using ( Cond ; Sub ; isFilter )

module General = K11.CountableCohen 𝒮 NG.extensional NG.≈ˢ-paths
  NG.hasPair NG.hasUnion NG.hasSeparation pow κ w lem

open General public using ( base ; module CG ; module FromCarrier ; generic-truncated )
