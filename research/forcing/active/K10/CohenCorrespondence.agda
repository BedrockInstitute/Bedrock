{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import K10.CohenAgreementSeam
import K10.CohenValSeam
import K9.NameGround

module K10.CohenCorrespondence
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
open import CodedVocabulary 𝒮 using ( denseΔ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( ≈ˢ-paths ; module C )
module Seam = K10.CohenAgreementSeam 𝒮 families accessible images pow κ w lem
module FS = Seam.GI.FS
module VS = K10.CohenValSeam 𝒮 families accessible images pow κ w lem NG.≈ˢ-paths

boolean-val = VS.val
boolean-law-∈ = VS.law-∈
boolean-law-≐ = VS.law-≐

module AtGeneric (G : FS.Sub)
  (fil : FS.isFilter G)
  (meets : (d : S) → ⟨ d ⊆ˢ NG.C.carrier ⟩
         → ⟨ denseΔ NG.C.carrier NG.C.order d ⟩
         → ⟨ ⋁ FS.Cond (λ q → (q FS.∈ᴾ G) ⊓ (fst q ∈ˢ d)) ⟩)
  where

  module FG = Seam.FromGeneric G fil meets

  poset-boolean-eq = FG.≈-agree
  poset-boolean-mem = FG.∈-agree
  reverse-surjective = FG.ext-surjective
