{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import Cubical.HITs.PropositionalTruncation as PT
import K10.CohenBooleanInjMaps
import K10.CohenBooleanInjRn
import K10.CohenBooleanInjInner
import K10.CohenBooleanInjTriple
import K10.CohenBooleanInjAtom

-- Compose the four extraction layers. Each layer is already checked.

module K10.CohenBooleanInjPipe
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
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import CodedVocabulary 𝒮 using ( isKPairΔ ; refinesΔ )
open PT using ( ∣_∣₁ ; ∥_∥₁ ; squash₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module Maps = K10.CohenBooleanInjMaps 𝒮 families accessible images pow κ w lem paths
module Rn = K10.CohenBooleanInjRn 𝒮 families accessible images pow κ w lem paths
module Inn = K10.CohenBooleanInjInner 𝒮 families accessible images pow κ w lem paths
module Tr = K10.CohenBooleanInjTriple 𝒮 families accessible images pow κ w lem paths
module Atm = K10.CohenBooleanInjAtom 𝒮 families accessible images pow κ w lem paths

open Maps using ( hitFo )

record HitParts (y ξ p σ : S) : Type ℓ where
  field
    r n pair τ b : S
    r∈c : ⟨ r ∈ˢ Maps.Chk.carrier ⟩
    n∈w : ⟨ n ∈ˢ w ⟩
    y-pair : ⟨ isKPairΔ y r n ⟩
    r≼p : ⟨ refinesΔ Maps.Chk.order r p ⟩
    pair-ξn : ⟨ isKPairΔ pair ξ n ⟩
    r∈b : ⟨ r ∈ˢ b ⟩

parts-same-rn : (y p σ : S) {ξ ξ' : S}
  → (p1 : HitParts y ξ p σ) (p2 : HitParts y ξ' p σ)
  → (HitParts.r p1 ≡ HitParts.r p2) × (HitParts.n p1 ≡ HitParts.n p2)
parts-same-rn y p σ p1 p2 =
  Maps.Chk.ordered-components y
    (HitParts.r p1) (HitParts.n p1)
    (HitParts.r p2) (HitParts.n p2)
    (HitParts.y-pair p1) (HitParts.y-pair p2)

hit-parts : (σ p ω₁ y ξ : S)
  → ⟨ (y ∷ ξ ∷ []) ⊨ hitFo σ p ω₁ ⟩
  → ∥ HitParts y ξ p σ ∥₁
hit-parts σ p ω₁ y ξ h =
  PT.rec squash₁
    (λ { (r , n , r∈c , n∈w , ypn , inner) →
      let om = Inn.hit-order-mem ω₁ n r y ξ p σ Maps.BAT.B inner
          r≼ = om .fst
          hmem = om .snd
      in PT.rec squash₁
        (λ { (pair , τ , b , hatom) →
          let parts = Atm.hit-atom-parts ω₁ b τ pair n r y ξ p σ Maps.BAT.B hatom
          in ∣ record
            { r = r ; n = n ; pair = pair ; τ = τ ; b = b
            ; r∈c = r∈c ; n∈w = n∈w ; y-pair = ypn ; r≼p = r≼
            ; pair-ξn = parts .fst
            ; r∈b = parts .snd .snd .snd
            } ∣₁ })
        (Tr.hit-triple ω₁ n r y ξ p σ Maps.BAT.B hmem) })
    (Rn.hit-rn σ p ω₁ y ξ h)

unique-if-same-pair : (y p σ : S) {ξ ξ' : S}
  → (p1 : HitParts y ξ p σ) (p2 : HitParts y ξ' p σ)
  → HitParts.pair p1 ≡ HitParts.pair p2
  → ⟨ ξ ≈ˢ ξ' ⟩
unique-if-same-pair y p σ {ξ} {ξ'} p1 p2 eq =
  subst ⟨_⟩ (sym (paths ξ ξ')) (fst ξn)
  where
  rn = parts-same-rn y p σ p1 p2
  ξn = Maps.Chk.ordered-components (HitParts.pair p1)
    ξ (HitParts.n p1) ξ' (HitParts.n p1)
    (HitParts.pair-ξn p1)
    (subst (λ t → ⟨ isKPairΔ t ξ' (HitParts.n p1) ⟩) (sym eq)
      (subst (λ n → ⟨ isKPairΔ (HitParts.pair p2) ξ' n ⟩) (sym (snd rn))
        (HitParts.pair-ξn p2)))

-- HitUnique, assembled from hit-parts and unique-if-same-pair, given
-- that the two extracted ground pairs coincide. The pair-equality
-- hypothesis is Force.pair-at-r plus InjPair, supplied by a consumer
-- that must not import this file together with Force.

module FromPairsEq (σ p : S)
  (pairs-eq : {y ξ ξ' : S}
    (p1 : HitParts y ξ p σ) (p2 : HitParts y ξ' p σ)
    → HitParts.pair p1 ≡ HitParts.pair p2)
  where

  unique : (ω₁ ξ ξ' y : S)
    → ⟨ ξ ∈ˢ ω₁ ⟩ → ⟨ ξ' ∈ˢ ω₁ ⟩
    → ⟨ y ∈ˢ Maps.Chk.product Maps.Chk.carrier w ⟩
    → ⟨ (y ∷ ξ ∷ []) ⊨ hitFo σ p ω₁ ⟩
    → ⟨ (y ∷ ξ' ∷ []) ⊨ hitFo σ p ω₁ ⟩
    → ⟨ ξ ≈ˢ ξ' ⟩
  unique ω₁ ξ ξ' y _ _ _ h h' =
    PT.rec (snd (ξ ≈ˢ ξ'))
      (λ p1 → PT.rec (snd (ξ ≈ˢ ξ'))
        (λ p2 → unique-if-same-pair y p σ p1 p2 (pairs-eq p1 p2))
        (hit-parts σ p ω₁ y ξ' h'))
      (hit-parts σ p ω₁ y ξ h)
