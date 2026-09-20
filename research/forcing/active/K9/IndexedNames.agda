{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile

module K9.IndexedNames
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import K9.NameGround

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
private
  module NG = K9.NameGround 𝒮 families accessible images pow κ w
  module GS = NG.GS
  module K = NG.K
  module Image = NG.Image
  module Check = NG.Check
  module Union = NG.Union

opaque
  indexedCode : S → (S → S) → S
  indexedCode A f = Union.bigUnion (Image.imageOn A (λ a → Check.spread (f a)))

  indexed-spec : (A : S) (f : S → S) (e : S) → (e ∈ˢ indexedCode A f)
    ≡ ⋁ S (λ a → (a ∈ˢ A) ⊓ ⋁ S (λ p → (p ∈ˢ NG.C.carrier) ⊓ (e ≈ˢ K.entry (f a) p)))
  indexed-spec A f e = ⇔toPath forward backward
    where
    Target : Ω
    Target = ⋁ S (λ a → (a ∈ˢ A) ⊓ ⋁ S (λ p → (p ∈ˢ NG.C.carrier) ⊓ (e ≈ˢ K.entry (f a) p)))

    forward : ⟨ e ∈ˢ indexedCode A f ⟩ → ⟨ Target ⟩
    forward h = PT.rec (snd Target)
      (λ { (u , hu , eu) → PT.map
        (λ { (a , ha , eq) → a , ha , subst ⟨_⟩ (Check.spread-spec (f a) e)
          (subst (λ z → ⟨ e ∈ˢ z ⟩) (GS.≈→≡ eq) eu) })
        (subst ⟨_⟩ (Image.imageOn-spec A (λ a → Check.spread (f a)) u) hu) })
      (subst ⟨_⟩ (Union.bigUnion-spec (Image.imageOn A (λ a → Check.spread (f a))) e) h)

    backward : ⟨ Target ⟩ → ⟨ e ∈ˢ indexedCode A f ⟩
    backward = PT.rec (snd (e ∈ˢ indexedCode A f))
      (λ { (a , ha , ps) → subst ⟨_⟩
        (sym (Union.bigUnion-spec (Image.imageOn A (λ a → Check.spread (f a))) e))
        ∣ Check.spread (f a) , subst ⟨_⟩
          (sym (Image.imageOn-spec A (λ a → Check.spread (f a)) (Check.spread (f a))))
          ∣ a , ha , subst ⟨_⟩ (sym (NG.≈ˢ-paths (Check.spread (f a)) (Check.spread (f a)))) refl ∣₁
        , subst ⟨_⟩ (sym (Check.spread-spec (f a) e)) ps ∣₁ })

indexed-name : (A : S) (f : S → S)
  → ((a : S) → ⟨ a ∈ˢ A ⟩ → ⟨ K.IsName (f a) ⟩) → ⟨ K.IsName (indexedCode A f) ⟩
indexed-name A f valid = NG.entries-name (indexedCode A f) λ e he → PT.rec PT.squash₁
  (λ { (a , ha , ps) → PT.map (λ { (p , hp , ep) → f a , p , GS.≈→≡ ep , hp , valid a ha }) ps })
  (subst ⟨_⟩ (indexed-spec A f e) he)

indexed : S → (S → K.Name) → K.Name
indexed A f = indexedCode A (λ a → fst (f a)) , indexed-name A (λ a → fst (f a)) (λ a _ → snd (f a))

indexed-entry : (A : S) (f : S → S) (a p : S)
  → ⟨ a ∈ˢ A ⟩ → ⟨ p ∈ˢ NG.C.carrier ⟩ → ⟨ K.entry (f a) p ∈ˢ indexedCode A f ⟩
indexed-entry A f a p ha hp = subst ⟨_⟩ (sym (indexed-spec A f (K.entry (f a) p)))
  ∣ a , ha , ∣ p , hp , subst ⟨_⟩ (sym (NG.≈ˢ-paths (K.entry (f a) p) (K.entry (f a) p))) refl ∣₁ ∣₁

supportBound : S → (S → S) → S
supportBound = Image.imageOn

indexed-support : (A : S) (f : S → S) (x : S)
  → K.Child x (indexedCode A f) → ⟨ x ∈ˢ supportBound A f ⟩
indexed-support A f x = PT.rec (snd (x ∈ˢ supportBound A f))
  (λ { (b , hb) → PT.rec (snd (x ∈ˢ supportBound A f))
    (λ { (a , ha , ps) → PT.rec (snd (x ∈ˢ supportBound A f))
      (λ { (p , hp , ep) → subst ⟨_⟩ (sym (Image.imageOn-spec A f x))
        ∣ a , ha , subst ⟨_⟩ (sym (NG.≈ˢ-paths x (f a))) (fst (K.entry-inj (GS.≈→≡ ep))) ∣₁ }) ps })
    (subst ⟨_⟩ (indexed-spec A f (K.entry x b)) hb) })

module AtGeneric (G : NG.P.Sub) (positive : ⟨ NG.P.positive G ⟩) where
  private
    module At = NG.AtGeneric G
    module E = At.E
  open E using ( _≈[G]_; _∈[G]_ )

  indexed-value : (A : S) (f : S → S) (χ : S)
    → (χ ∈[G] indexedCode A f) ≡ ⋁ S (λ a → (a ∈ˢ A) ⊓ (χ ≈[G] f a))
  indexed-value A f χ = ⇔toPath forward backward
    where
    Target : Ω
    Target = ⋁ S (λ a → (a ∈ˢ A) ⊓ (χ ≈[G] f a))

    forward : ⟨ χ ∈[G] indexedCode A f ⟩ → ⟨ Target ⟩
    forward = PT.rec (snd Target)
      (λ { (x , active , eq) → PT.rec (snd Target)
        (λ { (b , hb , member , gb) → PT.rec (snd Target)
          (λ { (a , ha , ps) → PT.map
            (λ { (p , hp , ep) → a , ha , subst (λ y → ⟨ χ ≈[G] y ⟩)
              (fst (K.entry-inj (GS.≈→≡ ep))) eq }) ps })
          (subst ⟨_⟩ (indexed-spec A f (K.entry x b)) member) }) active })

    backward : ⟨ Target ⟩ → ⟨ χ ∈[G] indexedCode A f ⟩
    backward = PT.rec (snd (χ ∈[G] indexedCode A f))
      (λ { (a , ha , eq) → PT.rec (snd (χ ∈[G] indexedCode A f))
        (λ { (p , gp) → E.∈-congˡ (E.≈-sym eq)
          (E.entry-value (indexedCode A f) (f a) (fst p) (snd p) gp
            (indexed-entry A f a (fst p) ha (snd p))) }) positive })
