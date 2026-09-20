{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import K9.BooleanNameGround
import Cubical.HITs.PropositionalTruncation as PT

module K10.CohenNameIntro
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open PT using ( ∥_∥₁ ; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module BNG = K9.BooleanNameGround 𝒮 families accessible images pow κ w lem
open BNG using ( B ; module BK ; module NG )
open NG using ( ≈ˢ-paths )

≈→≡ : {a b : S} → ⟨ a ≈ˢ b ⟩ → a ≡ b
≈→≡ {a} {b} = subst ⟨_⟩ (≈ˢ-paths a b)

Listing : S → Type ℓ
Listing n =
  (e : S) → ⟨ e ∈ˢ n ⟩
  → ∥ Σ[ x ∈ S ] Σ[ p ∈ S ]
      ((e ≡ BK.entry x p) × (⟨ p ∈ˢ B ⟩ × ⟨ BK.IsName x ⟩)) ∥₁

Spec : (n cands : S) (candEntry : S → S) → Type (ℓ-suc ℓ)
Spec n cands candEntry =
  (e : S) → (e ∈ˢ n)
    ≡ ⋁ S (λ σ → ⋁ ⟨ σ ∈ˢ cands ⟩ (λ _ → e ≈ˢ candEntry σ))

EntryData : (cands : S) (candEntry : S → S) → Type ℓ
EntryData cands candEntry =
  (σ : S) → ⟨ σ ∈ˢ cands ⟩
  → Σ[ x ∈ S ] Σ[ p ∈ S ]
      ((candEntry σ ≡ BK.entry x p) × (⟨ p ∈ˢ B ⟩ × ⟨ BK.IsName x ⟩))

opaque
  mkListing : (n cands : S) (candEntry : S → S)
            → Spec n cands candEntry
            → EntryData cands candEntry
            → Listing n
  mkListing n cands candEntry spec payload e he = PT.rec PT.squash₁
    (λ { (σ , inner) → PT.rec PT.squash₁
      (λ { (hσ , eq) →
        let (x , p , path , hp , hx) = payload σ hσ
        in ∣ x , p , ≈→≡ eq ∙ path , hp , hx ∣₁ })
      inner })
    (subst ⟨_⟩ (spec e) he)

opaque
  mkName : (n : S) → Listing n → ⟨ BK.IsName n ⟩
  mkName n listing = BK.name-intro n shape hered
    where
    shape : ⟨ BK.Shape n ⟩
    shape e he = PT.map
      (λ { (x , p , eq , hp , _) → x , p , eq , hp })
      (listing e he)

    hered : (x : S) → BK.Child x n → ⟨ BK.IsName x ⟩
    hered x ch = PT.rec (snd (BK.IsName x))
      (λ { (b , he) → PT.rec (snd (BK.IsName x))
        (λ { (x' , p , eq , _ , hx') →
          subst (λ u → ⟨ BK.IsName u ⟩) (sym (fst (BK.entry-inj eq))) hx' })
        (listing (BK.entry x b) he) })
      ch
