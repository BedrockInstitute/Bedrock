{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K7.FunctionalValues
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (mem-congˡ : (x y z : ZFStructure.S 𝒮)
    → ⟨ ZFStructure._≈ˢ_ 𝒮 x y ⟩
    → ZFStructure._∈ˢ_ 𝒮 x z ≡ ZFStructure._∈ˢ_ 𝒮 y z)
  (mem-congʳ : (x y z : ZFStructure.S 𝒮)
    → ⟨ ZFStructure._≈ˢ_ 𝒮 y z ⟩
    → ZFStructure._∈ˢ_ 𝒮 x y ≡ ZFStructure._∈ˢ_ 𝒮 x z)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_; ∃̇_ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import CardinalBridge
import CodedVocabulary
import K7.CardinalOrder

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module CB = CardinalBridge 𝒮
module CV = CodedVocabulary 𝒮
module CO = K7.CardinalOrder 𝒮
module Order = CO.Order ext mem-congˡ mem-congʳ

-- The bounded positive pair predicate and the biconditional predicate agree
-- in an extensional structure. The positive predicate already contains the
-- two required witnesses, so this direction spends no Pairing axiom.

positive-pair : (p x y : S) → ⟨ CV.isKPairΔ p x y ⟩
  → ⟨ CB.isKPair p x y ⟩
positive-pair p x y h t = h .snd .snd t , PT.rec (snd (t ∈ˢ p))
  (λ { (inl s) → PT.rec (snd (t ∈ˢ p))
       (λ { (w , hw , sw) → Order.mem-inˡ w t p
         (Order.sgl-unique w t x sw s) hw }) (h .fst)
     ; (inr u) → PT.rec (snd (t ∈ˢ p))
       (λ { (w , hw , uw) → Order.mem-inˡ w t p
         (Order.pr-unique w t x y uw u) hw }) (h .snd .fst) })

-- The converse obtains the singleton and unordered-pair witnesses from
-- Pairing, then puts them into p by the biconditional's reverse implication.

pair-positive : OrdinaryProfile.Pairing 𝒮 → (p x y : S)
  → ⟨ CB.isKPair p x y ⟩ → ⟨ CV.isKPairΔ p x y ⟩
pair-positive pair p x y h =
  PT.map (λ { (w , s) → w , h w .snd ∣ inl s ∣₁ , s }) (Order.sglOf pair x)
  , PT.map (λ { (w , u) → w , h w .snd ∣ inr u ∣₁ , u }) (Order.prOf pair x y)
  , λ t → h t .fst

-- Retain the positive presentation to verify the formula migration.

positiveValueFo : S → Formula S 2
positiveValueFo f = ∃̇ (CV.prAtˢ zero (suc zero) (suc (suc zero))
  ∧̇ (var zero ∈̇ con f))

valueFo : S → Formula S 2
valueFo f = ∃̇ (CB.PairφK ∧̇ (var zero ∈̇ con f))

value-reading : (f x y : S) → ((x ∷ y ∷ []) ⊨ valueFo f)
  ≡ ⋁ S (λ p → CB.isKPair p x y ⊓ (p ∈ˢ f))
value-reading f x y = refl

value-formulas-agree : OrdinaryProfile.Pairing 𝒮 → (f x y : S)
  → ((x ∷ y ∷ []) ⊨ positiveValueFo f) ≡ ((x ∷ y ∷ []) ⊨ valueFo f)
value-formulas-agree pair f x y = ⇔toPath
  (PT.map (λ { (p , hp , hf) → p , positive-pair p x y hp , hf }))
  (PT.map (λ { (p , hp , hf) → p , pair-positive pair p x y hp , hf }))

functional-values : (f x y z : S) → ⟨ CB.isFunction f ⟩
  → ⟨ (x ∷ y ∷ []) ⊨ valueFo f ⟩
  → ⟨ (x ∷ z ∷ []) ⊨ valueFo f ⟩ → ⟨ y ≈ˢ z ⟩
functional-values f x y z h a b = PT.rec (snd (y ≈ˢ z))
  (λ { (p , kp , hp) → PT.rec (snd (y ≈ˢ z))
    (λ { (q , kq , hq) → h .snd p hp q hq x y z
      (kp , kq) }) b }) a

functional-formula-values : (f x y z : S)
  → ⟨ (f ∷ []) ⊨ CB.IsFunctionφ ⟩
  → ⟨ (x ∷ y ∷ []) ⊨ valueFo f ⟩
  → ⟨ (x ∷ z ∷ []) ⊨ valueFo f ⟩ → ⟨ y ≈ˢ z ⟩
functional-formula-values f x y z h = functional-values f x y z
  (subst ⟨_⟩ (CB.IsFunction-bridge f) h)

surjection-value : (f a b y : S)
  → ⟨ CO.isSurjection f a b ⟩ → ⟨ y ∈ˢ b ⟩
  → ⟨ ⋁ S (λ x → (x ∈ˢ a) ⊓ ((x ∷ y ∷ []) ⊨ valueFo f)) ⟩
surjection-value f a b y h hy = PT.rec
  (snd (⋁ S (λ x → (x ∈ˢ a) ⊓ ((x ∷ y ∷ []) ⊨ valueFo f))))
  (λ { (x , k) → PT.map
    (λ { (p , hx , hp , kp) → x , hx , ∣ p , kp , hp ∣₁ }) k })
  (h .snd .snd .snd y hy)
