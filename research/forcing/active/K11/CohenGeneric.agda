{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import CodedCompletion
import K8.Cohen
import K11.CountableCohen

module K11.CohenGeneric
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open hPropStructure 𝒮

module NF = NameKernel.Families families
module NS = NameKernel.Sets NF.sets
module NG = NameKernel.Core NS.core
module C = K8.Cohen 𝒮 NG.extensional NG.≈ˢ-paths NG.hasPair NS.hasUnion pow NS.hasSeparation κ w
  using ( presentation ; laws ; module GS ; module PM )
module K = CodedCompletion.Core 𝒮 NG.extensional pow NS.hasSeparation NG.≈ˢ-paths
  C.presentation C.laws
module FS = K.FS
open FS using ( Cond ; Sub ; isFilter )

module General = K11.CountableCohen 𝒮 NG.extensional NG.≈ˢ-paths
  NG.hasPair NS.hasUnion NS.hasSeparation pow κ w lem

open General public using ( base ; module CG ; module FromCarrier ; generic-truncated )
