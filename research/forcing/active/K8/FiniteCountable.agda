{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.FiniteCountable
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair : OrdinaryProfile.Pairing 𝒮)
  (un : OrdinaryProfile.Union 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (sep : OrdinaryProfile.Separation 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (seed : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import Base.Classical using ( LEM )
open import CodedVocabulary 𝒮 using ( subsetΔ; subsetAtˢ; sepAt; sepAt-reading )
open import K8.FiniteVocabulary 𝒮 using ( finiteIn )
import K8.GroundSets
import K8.FiniteEnumeration
import K7.CardinalOrder
import CardinalBridge
module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module FE = K8.FiniteEnumeration 𝒮 ext paths pair un pow sep find seed
module CB = CardinalBridge 𝒮
open import Cubical.Data.Sum using ( _⊎_ ) renaming ( inl to inl⊎; inr to inr⊎ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module CO = K7.CardinalOrder.Order 𝒮 ext
  (λ x y z e → cong (_∈ˢ z) (GS.≈→≡ e))
  (λ x y z e → cong (x ∈ˢ_) (GS.≈→≡ e))

omega-transitive : (w : S) → ⟨ CB.isOmega w ⟩ → (n : S) → ⟨ n ∈ˢ w ⟩
  → ⟨ subsetΔ n w ⟩
omega-transitive w hw n hn = snd (subst ⟨_⟩ (part-spec n)
  (snd hw part closedPart n hn))
  where
  φ : Formula S 1
  φ = sepAt (subsetAtˢ zero (suc zero)) (w ∷ [])

  opaque
    part : S
    part = GS.separator w φ

    part-spec : (x : S) → (x ∈ˢ part) ≡ ((x ∈ˢ w) ⊓ subsetΔ x w)
    part-spec x = GS.separator-spec w φ x
      ∙ cong ((x ∈ˢ w) ⊓_) (sepAt-reading (subsetAtˢ zero (suc zero)) (w ∷ []) x)

  closedPart : ⟨ CB.isInductive part ⟩
  closedPart = PT.map (λ { (e , he , emptyE) → e ,
      subst ⟨_⟩ (sym (part-spec e)) (he , (λ z hz → Empty.rec* (emptyE z hz)))
      , emptyE }) (fst (fst hw))
    , (λ x hx → PT.map (λ { (s , hs , succ) → s ,
      subst ⟨_⟩ (sym (part-spec s)) (hs , below x hx s succ) , succ })
      (snd (fst hw) x (fst (subst ⟨_⟩ (part-spec x) hx))))
    where
    below : (x : S) → ⟨ x ∈ˢ part ⟩ → (s : S) → ⟨ CB.isSuccOf s x ⟩
      → ⟨ subsetΔ s w ⟩
    below x hx s succ z hz = PT.rec (snd (z ∈ˢ w))
      (λ { (inl⊎ zx) → snd data' z zx
         ; (inr⊎ eq) → subst (λ t → ⟨ t ∈ˢ w ⟩) (sym (GS.≈→≡ eq)) (fst data') })
      (snd (snd succ) z hz)
      where
      data' : ⟨ (x ∈ˢ w) ⊓ subsetΔ x w ⟩
      data' = subst ⟨_⟩ (part-spec x) hx

finite-countable : LEM ℓ → (w : S) → ⟨ CB.isOmega w ⟩
  → (X a : S) → ⟨ finiteIn X a ⟩ → ⟨ CB.injectable a w ⟩
finite-countable lem w hw X a ha = PT.rec (snd (CB.injectable a w))
  (λ { (n , hn , inj) → CO.injectable-mono-cod a n w (omega-transitive w hw n hn) inj })
  (FE.finite-size-bound lem w hw X a ha)
