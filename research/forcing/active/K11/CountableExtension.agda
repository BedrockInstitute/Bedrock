{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import CardinalBridge
import K10.CohenTheorem
import K11.CohenGeneric
open import Cubical.HITs.PropositionalTruncation using ( ∥_∥₁ )

module K11.CountableExtension
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  (hw : ⟨ CardinalBridge.isOmega 𝒮 w ⟩)
  (ν : ℕ → ZFStructure.S 𝒮)
  (ν-covers : (x : ZFStructure.S 𝒮)
    → ∥ Σ[ n ∈ ℕ ] ⟨ ZFStructure._≈ˢ_ 𝒮 (ν n) x ⟩ ∥₁)
  where

open import FOL.ZFStructure using ( module hPropStructure )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module Supplier = K11.CohenGeneric 𝒮 families pow κ w lem
  using ( module General; module FS; module K )
module Constructed = Supplier.General.FromCarrier ν ν-covers
  using ( genericSet; generic )

G : Supplier.FS.Sub
G = Constructed.genericSet

generic : Supplier.K.isGeneric G
generic = Constructed.generic

module Theorem = K10.CohenTheorem
  𝒮 families accessible images pow find κ w lem hw
  using ( module AtGeneric )

module AtGeneric = Theorem.AtGeneric G generic
  using ( module WithPreservedCardinals )

module WithPreservedCardinals = AtGeneric.WithPreservedCardinals
