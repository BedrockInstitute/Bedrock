{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import CodedCompletion
import K8.Cohen
import K11.CountableGround

module K11.CountableCohen
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair : OrdinaryProfile.Pairing 𝒮)
  (un : OrdinaryProfile.Union 𝒮)
  (sep : OrdinaryProfile.Separation 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open hPropStructure 𝒮

module C = K8.Cohen 𝒮 ext paths pair un pow sep κ w
  using ( presentation ; laws ; module GS ; module PM )
module K = CodedCompletion.Core 𝒮 ext pow sep paths
  C.presentation C.laws
module FS = K.FS
open FS using ( Cond ; Sub ; isFilter )

base : Cond
base = C.GS.empty , C.PM.empty-in-carrier

module CG = K11.CountableGround 𝒮 ext pow sep paths
  C.presentation C.laws lem

module FromCarrier (ν : ℕ → S)
  (ν-covers : (x : S) → PT.∥ Σ[ n ∈ ℕ ] ⟨ ν n ≈ˢ x ⟩ ∥₁) where

  private
    module FC = CG.FromCarrier ν ν-covers base
  genericSet : Sub
  genericSet = FC.GF.genericSet
  genericFilter : isFilter genericSet
  genericFilter = FC.GF.genericFilter
  generic : K.isGeneric genericSet
  generic = FC.GF.generic

generic-truncated :
  (t : PT.∥ Σ[ ν ∈ (ℕ → S) ] ((x : S) → PT.∥ Σ[ n ∈ ℕ ] ⟨ ν n ≈ˢ x ⟩ ∥₁) ∥₁)
  → PT.∥ Σ[ G ∈ Sub ] K.isGeneric G ∥₁
generic-truncated t = CG.generic-truncated base t

from-carrier : (ν : ℕ → S)
  → ((x : S) → PT.∥ Σ[ n ∈ ℕ ] ⟨ ν n ≈ˢ x ⟩ ∥₁)
  → Σ[ G ∈ Sub ] K.isGeneric G
from-carrier ν covers = CG.carrier-generic ν covers base
