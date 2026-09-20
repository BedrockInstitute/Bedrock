{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import CodedCompletion
import K11.CohenGeneric
import K11.GenericFilter
import K9.NameGround
import K8.Cohen

module K11.Corollary
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
open PT using ( ∣_∣₁ ; ∥_∥₁ )

open hPropStructure 𝒮

module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( extensional ; ≈ˢ-paths ; hasSeparation ; hasPair ; hasUnion )
module C = K8.Cohen 𝒮 NG.extensional NG.≈ˢ-paths NG.hasPair NG.hasUnion
  pow NG.hasSeparation κ w
  using ( presentation ; laws )
module Core = CodedCompletion.Core 𝒮 NG.extensional pow NG.hasSeparation
  NG.≈ˢ-paths C.presentation C.laws
module FS = Core.FS
open FS using ( Cond ; Sub )

module Exists = K11.CohenGeneric 𝒮 families accessible images pow κ w lem
module Enumerated = K11.GenericFilter 𝒮 NG.extensional pow NG.hasSeparation
  NG.≈ˢ-paths C.presentation C.laws lem

from-carrier :
  (ν : ℕ → S)
  → ((x : S) → PT.∥ Σ[ n ∈ ℕ ] ⟨ ν n ≈ˢ x ⟩ ∥₁)
  → Σ[ G ∈ Sub ] Core.isGeneric G
from-carrier ν covers = Exists.CG.carrier-generic ν covers Exists.base

from-carrier-truncated :
  PT.∥ Σ[ ν ∈ (ℕ → S) ] ((x : S) → PT.∥ Σ[ n ∈ ℕ ] ⟨ ν n ≈ˢ x ⟩ ∥₁) ∥₁
  → PT.∥ Σ[ G ∈ Sub ] Core.isGeneric G ∥₁
from-carrier-truncated = Exists.generic-truncated

from-enumerations :
  (condEnum : ℕ → Cond)
  → (condCover : (p : Cond) → Σ[ n ∈ ℕ ] (condEnum n ≡ p))
  → (denseEnum : ℕ → S)
  → (dense-dense : (n : ℕ) → ⟨ Core.denseᴵ (denseEnum n) ⟩)
  → (dense-sub : (n : ℕ) → ⟨ Core.subsetOf (denseEnum n) ⟩)
  → (denseCover : (d : S) → ⟨ Core.subsetOf d ⟩ → ⟨ Core.denseᴵ d ⟩
                 → Σ[ n ∈ ℕ ] (denseEnum n ≡ d))
  → Σ[ G ∈ Sub ] Core.isGeneric G
from-enumerations condEnum condCover denseEnum dense-dense dense-sub denseCover =
  GF.genericSet , GF.generic
  where
  module GF = Enumerated.FromEnumerations condEnum condCover denseEnum
    dense-dense dense-sub denseCover
