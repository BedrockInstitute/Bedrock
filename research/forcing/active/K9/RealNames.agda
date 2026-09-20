{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile

module K9.RealNames
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import CodedVocabulary 𝒮 using ( refinesΔ; orderAtˢ; sepAt; sepAt-reading )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import K9.NameGround

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
module Ground = K9.NameGround 𝒮 families accessible images pow κ w
  using ( module GS; module Union; module C; module K; module Image; module Check
        ; entries-name; chk-name; ≈ˢ-paths )
private
  module GS = Ground.GS
  module C = Ground.C
  module K = Ground.K
  module Image = Ground.Image
  module Check = Ground.Check
  module Union = Ground.Union

assignmentFormula : S → S → Formula S 1
assignmentFormula α n = sepAt (orderAtˢ zero (suc zero) (suc (suc zero)))
  (C.coordinate α n ∷ C.bit₁ ∷ [])

opaque
  assignments : S → S → S
  assignments α n = GS.separator C.carrier (assignmentFormula α n)

  assignments-spec : (α n p : S) → (p ∈ˢ assignments α n)
    ≡ ((p ∈ˢ C.carrier) ⊓ refinesΔ p (C.coordinate α n) C.bit₁)
  assignments-spec α n p = GS.separator-spec C.carrier (assignmentFormula α n) p
    ∙ cong ((p ∈ˢ C.carrier) ⊓_)
      (sepAt-reading (orderAtˢ zero (suc zero) (suc (suc zero)))
        (C.coordinate α n ∷ C.bit₁ ∷ []) p)

opaque
  layer : S → S → S
  layer α n = Image.imageOn (assignments α n) (K.entry (Check.chk n))

  layer-spec : (α n e : S) → (e ∈ˢ layer α n)
    ≡ ⋁ S (λ p → (p ∈ˢ assignments α n) ⊓ (e ≈ˢ K.entry (Check.chk n) p))
  layer-spec α n = Image.imageOn-spec (assignments α n) (K.entry (Check.chk n))

opaque
  realCode : S → S
  realCode α = Union.bigUnion (Image.imageOn w (layer α))

  real-spec : (α e : S) → (e ∈ˢ realCode α)
    ≡ ⋁ S (λ n → (n ∈ˢ w) ⊓ ⋁ S (λ p → (p ∈ˢ C.carrier) ⊓
        (refinesΔ p (C.coordinate α n) C.bit₁ ⊓ (e ≈ˢ K.entry (Check.chk n) p))))
  real-spec α e = ⇔toPath forward backward
    where
    Target : Ω
    Target = ⋁ S (λ n → (n ∈ˢ w) ⊓ ⋁ S (λ p → (p ∈ˢ C.carrier) ⊓
      (refinesΔ p (C.coordinate α n) C.bit₁ ⊓ (e ≈ˢ K.entry (Check.chk n) p))))

    forward : ⟨ e ∈ˢ realCode α ⟩ → ⟨ Target ⟩
    forward he = PT.rec (snd Target)
      (λ { (L , hL , eL) → PT.rec (snd Target)
        (λ { (n , hn , eq) → PT.map (λ { (p , hp , ep) → n , hn ,
          ∣ p , fst (subst ⟨_⟩ (assignments-spec α n p) hp) ,
            snd (subst ⟨_⟩ (assignments-spec α n p) hp) , ep ∣₁ })
          (subst ⟨_⟩ (layer-spec α n e)
            (subst (λ z → ⟨ e ∈ˢ z ⟩) (GS.≈→≡ eq) eL)) })
        (subst ⟨_⟩ (Image.imageOn-spec w (layer α) L) hL) })
      (subst ⟨_⟩ (Union.bigUnion-spec (Image.imageOn w (layer α)) e) he)

    backward : ⟨ Target ⟩ → ⟨ e ∈ˢ realCode α ⟩
    backward = PT.rec (snd (e ∈ˢ realCode α))
      (λ { (n , hn , ps) → subst ⟨_⟩ (sym (Union.bigUnion-spec (Image.imageOn w (layer α)) e))
        ∣ layer α n , subst ⟨_⟩ (sym (Image.imageOn-spec w (layer α) (layer α n)))
          ∣ n , hn , subst ⟨_⟩ (sym (Ground.≈ˢ-paths (layer α n) (layer α n))) refl ∣₁
          , subst ⟨_⟩ (sym (layer-spec α n e))
            (PT.map (λ { (p , hp , bit , ep) → p ,
              subst ⟨_⟩ (sym (assignments-spec α n p)) (hp , bit) , ep }) ps) ∣₁ })

real-name : (α : S) → ⟨ K.IsName (realCode α) ⟩
real-name α = Ground.entries-name (realCode α) λ e he → PT.rec PT.squash₁
  (λ { (n , hn , ps) → PT.map (λ { (p , hp , bit , ep) → Check.chk n , p ,
    GS.≈→≡ ep , hp , Ground.chk-name n }) ps }) (subst ⟨_⟩ (real-spec α e) he)

real : S → K.Name
real α = realCode α , real-name α

real-entry : (α n p : S) → ⟨ n ∈ˢ w ⟩ → ⟨ p ∈ˢ C.carrier ⟩
  → ⟨ refinesΔ p (C.coordinate α n) C.bit₁ ⟩ → ⟨ K.entry (Check.chk n) p ∈ˢ realCode α ⟩
real-entry α n p hn hp bit = subst ⟨_⟩ (sym (real-spec α (K.entry (Check.chk n) p)))
  ∣ n , hn , ∣ p , hp , bit , subst ⟨_⟩
    (sym (Ground.≈ˢ-paths (K.entry (Check.chk n) p) (K.entry (Check.chk n) p))) refl ∣₁ ∣₁

opaque
  supportBound : S
  supportBound = Image.imageOn w Check.chk

  support-spec : (x : S) → (x ∈ˢ supportBound)
    ≡ ⋁ S (λ n → (n ∈ˢ w) ⊓ (x ≈ˢ Check.chk n))
  support-spec = Image.imageOn-spec w Check.chk

real-support : (α x : S) → K.Child x (realCode α) → ⟨ x ∈ˢ supportBound ⟩
real-support α x = PT.rec (snd (x ∈ˢ supportBound))
  (λ { (b , hb) → PT.rec (snd (x ∈ˢ supportBound))
    (λ { (n , hn , ps) → PT.rec (snd (x ∈ˢ supportBound))
      (λ { (p , hp , bit , ep) → subst ⟨_⟩ (sym (support-spec x))
        ∣ n , hn , subst ⟨_⟩ (sym (Ground.≈ˢ-paths x (Check.chk n)))
          (K.entry-inj (GS.≈→≡ ep) .fst) ∣₁ }) ps })
    (subst ⟨_⟩ (real-spec α (K.entry x b)) hb) })
