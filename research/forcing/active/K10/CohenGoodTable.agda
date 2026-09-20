{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import NameSupport
import OrdinaryProfile
import CodedVocabulary
import K4.AtomicGraph
import K9.BooleanNameGround

module K10.CohenGoodTable
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ ; ∥_∥₁ )
open import CodedVocabulary 𝒮 using ( isKPairΔ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module BG = K9.BooleanNameGround 𝒮 families accessible images pow κ w lem
  using ( B ; module BK )
module ISB = NameSupport.Instantiate.BG 𝒮 (NameKernel.Families.sets families)
  accessible BG.B
  using ( kpair-unique )
module AG = K4.AtomicGraph 𝒮 paths using ( entryΔ )

entryΔ-in : (H x y b p q : S) → ⟨ isKPairΔ p x y ⟩ → ⟨ isKPairΔ q p b ⟩ → ⟨ q ∈ˢ H ⟩
  → ⟨ AG.entryΔ H x y b ⟩
entryΔ-in H x y b p q hpq hqpb hqH = ∣ p , hpq , ∣ q , hqpb , hqH ∣₁ ∣₁

entryΔ-out : (H x y b : S) → ⟨ AG.entryΔ H x y b ⟩
  → ∥ Σ[ p ∈ S ] Σ[ q ∈ S ]
      (⟨ q ∈ˢ H ⟩ × ⟨ isKPairΔ q p b ⟩ × ⟨ isKPairΔ p x y ⟩) ∥₁
entryΔ-out H x y b =
  PT.rec PT.squash₁ (λ { (p , hpq , hin) →
    PT.map (λ { (q , hqpb , hqH) → p , q , hqH , hqpb , hpq }) hin })

entryΔ-pair-unique : (p q b p' b' : S)
  → ⟨ isKPairΔ q p b ⟩ → ⟨ isKPairΔ q p' b' ⟩
  → (p ≡ p') × (b ≡ b')
entryΔ-pair-unique p q b p' b' h₁ h₂ =
  BG.BK.entry-inj (sym (ISB.kpair-unique q p b h₁) ∙ ISB.kpair-unique q p' b' h₂)
