{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.OmegaSuccessor
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext   : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair  : OrdinaryProfile.Pairing 𝒮)
  (un    : OrdinaryProfile.Union 𝒮)
  (pow   : OrdinaryProfile.PowerSet 𝒮)
  (sep   : OrdinaryProfile.Separation 𝒮)
  (find  : OrdinaryProfile.FoundationInduction 𝒮)
  (seed  : ZFStructure.S 𝒮)
  where


open import FOL.ZFStructure using ( module hPropStructure )
open import CodedVocabulary 𝒮 using ( subsetΔ )
open import K8.FiniteVocabulary 𝒮 using ( emptyPred )
import K8.GroundSets
import K8.FiniteOperations
import K8.FinitePower
import K8.OmegaInduction
import K8.OmegaFinite
import K7.CardinalOrder
import CardinalBridge
open import GroundDescription 𝒮 ext paths using ( ext-path )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
module FO = K8.FiniteOperations 𝒮 ext paths pair un pow sep seed
module FP = K8.FinitePower 𝒮 ext paths pair un pow sep seed seed
module OI = K8.OmegaInduction 𝒮 ext paths pair un pow sep seed
module OF = K8.OmegaFinite 𝒮 ext paths pair un pow sep find seed
module CB = CardinalBridge 𝒮
module CO = K7.CardinalOrder.Order 𝒮 ext
  (λ x y z e → cong (_∈ˢ z) (GS.≈→≡ e))
  (λ x y z e → cong (x ∈ˢ_) (GS.≈→≡ e))

zeroSet : S
zeroSet = GS.empty

successor : S → S
successor n = FO.insert n n

successor-spec : (n : S) → ⟨ CB.isSuccOf (successor n) n ⟩
successor-spec n = FO.insert-witness n n

empty-unique : (e : S) → ⟨ emptyPred e ⟩ → e ≡ zeroSet
empty-unique e he = ext-path (λ z → ⇔toPath
  (λ hz → Empty.rec* (he z hz)) (λ hz → Empty.rec* (GS.empty-out z hz)))

successor-unique : (s n : S) → ⟨ CB.isSuccOf s n ⟩ → s ≡ successor n
successor-unique s n hs = FP.adjoin-unique s (successor n) n n hs (successor-spec n)

zero-in : (w : S) → ⟨ CB.isOmega w ⟩ → ⟨ zeroSet ∈ˢ w ⟩
zero-in w hw = PT.rec (snd (zeroSet ∈ˢ w))
  (λ { (e , he , ee) → subst (λ t → ⟨ t ∈ˢ w ⟩) (empty-unique e ee) he })
  (fst (fst hw))

successor-in : (w : S) → ⟨ CB.isOmega w ⟩
  → (n : S) → ⟨ n ∈ˢ w ⟩ → ⟨ successor n ∈ˢ w ⟩
successor-in w hw n hn = PT.rec (snd (successor n ∈ˢ w))
  (λ { (s , hs , sn) → subst (λ t → ⟨ t ∈ˢ w ⟩) (successor-unique s n sn) hs })
  (snd (fst hw) n hn)

omega-cases : (w : S) → ⟨ CB.isOmega w ⟩ → (n : S) → ⟨ n ∈ˢ w ⟩
  → ∥ (n ≡ zeroSet) ⊎ (Σ[ m ∈ S ] (⟨ m ∈ˢ w ⟩ × (n ≡ successor m))) ∥₁
omega-cases w hw n hn = PT.rec PT.squash₁
  (λ { (inl emptyN) → ∣ inl (empty-unique n emptyN) ∣₁
     ; (inr predN) → PT.map (λ { (m , hm , nm) →
         inr (m , hm , successor-unique n m nm) }) predN })
  (OI.omega-predecessor w hw n hn)

successor-not-zero : (n : S) → successor n ≡ zeroSet → Empty.⊥
successor-not-zero n eq = Empty.rec* (GS.empty-out n
  (subst (λ t → ⟨ n ∈ˢ t ⟩) eq (fst (successor-spec n))))

successor-injective : LEM ℓ → (w : S) → ⟨ CB.isOmega w ⟩
  → (n m : S) → ⟨ n ∈ˢ w ⟩ → ⟨ m ∈ˢ w ⟩
  → successor n ≡ successor m → n ≡ m
successor-injective lem w hw n m hn hm eq = PT.rec (isSetS n m) branch
  (CO.ord-compare find sep lem n m
    (OF.omega-members-ordinal w hw n hn) (OF.omega-members-ordinal w hw m hm))
  where
  impossible : (a b : S) → ⟨ CB.isOrdinal a ⟩
    → ⟨ a ∈ˢ b ⟩ → successor a ≡ successor b → Empty.⊥
  impossible a b oa ab same = PT.rec Empty.isProp⊥
    (λ { (inl ba) → CO.no-self find a (fst oa b ba a ab)
       ; (inr beq) → CO.no-self find a
           (subst (λ t → ⟨ a ∈ˢ t ⟩) (GS.≈→≡ beq) ab) })
    (snd (snd (successor-spec a)) b
      (subst (λ t → ⟨ b ∈ˢ t ⟩) (sym same) (fst (successor-spec b))))

  branch : ⟨ n ∈ˢ m ⟩ ⊎ ⟨ (n ≈ˢ m) ⊔ (m ∈ˢ n) ⟩ → n ≡ m
  branch (inl nm) = Empty.rec (impossible n m (OF.omega-members-ordinal w hw n hn) nm eq)
  branch (inr rest) = PT.rec (isSetS n m)
    (λ { (inl same) → GS.≈→≡ same
       ; (inr mn) → Empty.rec (impossible m n
           (OF.omega-members-ordinal w hw m hm) mn (sym eq)) }) rest

