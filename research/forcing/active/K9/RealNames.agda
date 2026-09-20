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
import InternalCohenReals

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
module Ground = K9.NameGround 𝒮 families accessible images pow κ w
  using ( module GS; module Union; module C; module K; module Check
        ; entries-name; chk-name; ≈ˢ-paths )
private
  module GS = Ground.GS
  module C = Ground.C
  module K = Ground.K
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

module Defined = InternalCohenReals 𝒮 families accessible pow κ w
  using ( realCode; real-spec; real-name; real; real-entry; supportBound; support-spec
        ; real-support; real-graph; real-image; module GS; entry-agrees )
open Defined public using
  ( realCode; real-spec; real-name; real; real-entry; supportBound; support-spec
  ; real-support; real-graph; real-image )

opaque
  layer : S → S → S
  layer α n = Defined.GS.product (Defined.GS.singleton (Check.chk n)) (assignments α n)

  layer-spec : (α n e : S) → (e ∈ˢ layer α n)
    ≡ ⋁ S (λ p → (p ∈ˢ assignments α n) ⊓ (e ≈ˢ K.entry (Check.chk n) p))
  layer-spec α n e = ⇔toPath forward backward
    where
    forward : ⟨ e ∈ˢ layer α n ⟩ →
      ⟨ ⋁ S (λ p → (p ∈ˢ assignments α n) ⊓ (e ≈ˢ K.entry (Check.chk n) p)) ⟩
    forward h = PT.map (λ { (t , p , ht , hp , kp) → p , hp ,
      subst ⟨_⟩ (sym (Ground.≈ˢ-paths e (K.entry (Check.chk n) p)))
        (Defined.GS.ordered-unique e t p kp ∙
          cong (λ j → Defined.GS.ordered j p)
            (GS.≈→≡ (Defined.GS.singleton-witness (Check.chk n) .snd t ht)) ∙
          Defined.entry-agrees (Check.chk n) p) })
      (Defined.GS.product-out (Defined.GS.singleton (Check.chk n)) (assignments α n) e h)

    backward : ⟨ ⋁ S (λ p → (p ∈ˢ assignments α n) ⊓ (e ≈ˢ K.entry (Check.chk n) p)) ⟩
      → ⟨ e ∈ˢ layer α n ⟩
    backward = PT.rec (snd (e ∈ˢ layer α n)) λ { (p , hp , eq) →
      subst (λ j → ⟨ j ∈ˢ layer α n ⟩)
        (Defined.entry-agrees (Check.chk n) p ∙ sym (GS.≈→≡ eq))
        (Defined.GS.product-in (Defined.GS.singleton (Check.chk n)) (assignments α n)
          (Check.chk n) p (Defined.GS.singleton-witness (Check.chk n) .fst) hp) }
