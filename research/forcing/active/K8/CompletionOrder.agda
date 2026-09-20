{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.CompletionOrder
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair : OrdinaryProfile.Pairing 𝒮)
  (un : OrdinaryProfile.Union 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (sep : OrdinaryProfile.Separation 𝒮)
  (seed : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import CodedVocabulary 𝒮 using ( refinesΔ; subsetΔ )
import Certificate
import CodedCompletion
import K8.SubsetOrder

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module G = Certificate 𝒮 ext paths
module CC = CodedCompletion 𝒮
module SO = K8.SubsetOrder 𝒮 ext paths pair un pow sep seed

module AtCompletion (𝔓 : G.Presentation) (cert : G.Over.CertifiedCompletion 𝔓) where
  module N = G.Nonzero 𝔓 cert sep

  presentation : CC.Presentation
  presentation = record
    { carrier = N.B⁺set
    ; order = SO.order N.B⁺set
    ; order-typed = SO.order-typed N.B⁺set
    ; inhabited = G.Presentation.inhabited N.B⁺ }

  module P = CC.Coded presentation

  laws : P.ForcingLaws
  laws = record
    { ≼ᴵ-refl = λ p hp → SO.refines-backward N.B⁺set p p hp hp (λ x hx → hx)
    ; ≼ᴵ-trans = λ r q p hr hq hp rq qp →
        SO.refines-backward N.B⁺set r p hr hp
          (λ x hx → SO.refines-forward N.B⁺set q p hq hp qp x
            (SO.refines-forward N.B⁺set r q hr hq rq x hx)) }

  order-reading : (u v : S) → ⟨ u ∈ˢ N.B⁺set ⟩ → ⟨ v ∈ˢ N.B⁺set ⟩
    → ⟨ OrdinaryProfile.iff 𝒮
      (refinesΔ (CC.Presentation.order presentation) u v)
      (subsetΔ u v) ⟩
  order-reading u v hu hv = SO.refines-forward N.B⁺set u v hu hv ,
    SO.refines-backward N.B⁺set u v hu hv

