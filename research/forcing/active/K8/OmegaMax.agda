{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.OmegaMax
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (sep : OrdinaryProfile.Separation 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At; _^_ )
import CardinalBridge
import K7.CardinalOrder
open import Cubical.Data.Sum using ( _⊎_ ) renaming ( inl to inl⊎; inr to inr⊎ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )
module CB = CardinalBridge 𝒮
≈→≡ : {x y : S} → ⟨ x ≈ˢ y ⟩ → x ≡ y
≈→≡ {x} {y} = subst ⟨_⟩ (paths x y)

module CO = K7.CardinalOrder.Order 𝒮 ext
  (λ x y z e → cong (_∈ˢ z) (≈→≡ e))
  (λ x y z e → cong (x ∈ˢ_) (≈→≡ e))

_≤ω_ : S → S → Ω
a ≤ω b = (a ∈ˢ b) ⊔ (a ≈ˢ b)

maxRel : S → S → S → Ω
maxRel m a b =
  ((a ∈ˢ b) ⊓ (m ≈ˢ b)) ⊔ (((a ∈ˢ b) ⇒ ⊥) ⊓ (m ≈ˢ a))

maxAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
maxAt m a b =
  ((var a ∈̇ var b) ∧̇ (var m ≐ var b)) ∨̇
  (((var a ∈̇ var b) ⇒̇ ⊥̇) ∧̇ (var m ≐ var a))

maxAt-reading : ∀ {n} (m a b : Fin n) (γ : S ^ n)
  → (γ ⊨ maxAt m a b) ≡ maxRel (lookup m γ) (lookup a γ) (lookup b γ)
maxAt-reading m a b γ = refl

maxω : S → S → S
maxω a b with lem (a ∈ˢ b)
... | inl⊎ _ = b
... | inr⊎ _ = a

maxRel-witness : (a b : S) → ⟨ maxRel (maxω a b) a b ⟩
maxRel-witness a b with lem (a ∈ˢ b)
... | inl⊎ ab = ∣ inl⊎ (ab , CO.≈-refl b) ∣₁
... | inr⊎ nab = ∣ inr⊎ ((λ h → Empty.rec (nab h)) , CO.≈-refl a) ∣₁

maxRel-unique : (m n a b : S) → ⟨ maxRel m a b ⟩ → ⟨ maxRel n a b ⟩ → m ≡ n
maxRel-unique m n a b = PT.rec (isPropΠ (λ _ → isSetS m n)) first
  where
  first : (⟨ (a ∈ˢ b) ⊓ (m ≈ˢ b) ⟩ ⊎ ⟨ ((a ∈ˢ b) ⇒ ⊥) ⊓ (m ≈ˢ a) ⟩)
    → ⟨ maxRel n a b ⟩ → m ≡ n
  first (inl⊎ (ab , mb)) = PT.rec (isSetS m n) λ
    { (inl⊎ (_ , nb)) → ≈→≡ mb ∙ sym (≈→≡ nb)
    ; (inr⊎ (nab , _)) → Empty.rec* (nab ab) }
  first (inr⊎ (nab , ma)) = PT.rec (isSetS m n) λ
    { (inl⊎ (ab , _)) → Empty.rec* (nab ab)
    ; (inr⊎ (_ , na)) → ≈→≡ ma ∙ sym (≈→≡ na) }

maxRel→maxω : (m a b : S) → ⟨ maxRel m a b ⟩ → m ≡ maxω a b
maxRel→maxω m a b h = maxRel-unique m (maxω a b) a b h (maxRel-witness a b)

maxω-choice : (a b : S) → ⟨ (maxω a b ≈ˢ a) ⊔ (maxω a b ≈ˢ b) ⟩
maxω-choice a b with lem (a ∈ˢ b)
... | inl⊎ _ = ∣ inr⊎ (CO.≈-refl b) ∣₁
... | inr⊎ _ = ∣ inl⊎ (CO.≈-refl a) ∣₁

left≤max : (a b : S) → ⟨ a ≤ω maxω a b ⟩
left≤max a b with lem (a ∈ˢ b)
... | inl⊎ ab = ∣ inl⊎ ab ∣₁
... | inr⊎ _ = ∣ inr⊎ (CO.≈-refl a) ∣₁

right≤max : (a b : S) → ⟨ CB.isOrdinal a ⟩ → ⟨ CB.isOrdinal b ⟩
  → ⟨ b ≤ω maxω a b ⟩
right≤max a b oa ob with lem (a ∈ˢ b)
... | inl⊎ _ = ∣ inr⊎ (CO.≈-refl b) ∣₁
... | inr⊎ notAB = PT.rec (snd (b ≤ω a)) choose
  (CO.ord-compare find sep lem b a ob oa)
  where
  choose : ⟨ b ∈ˢ a ⟩ ⊎ ⟨ (b ≈ˢ a) ⊔ (a ∈ˢ b) ⟩ → ⟨ b ≤ω a ⟩
  choose (inl⊎ ba) = ∣ inl⊎ ba ∣₁
  choose (inr⊎ rest) = PT.rec (snd (b ≤ω a))
    (λ { (inl⊎ eq) → ∣ inr⊎ eq ∣₁
       ; (inr⊎ ab) → Empty.rec (notAB ab) }) rest

maxω-ordinal : (a b : S) → ⟨ CB.isOrdinal a ⟩ → ⟨ CB.isOrdinal b ⟩
  → ⟨ CB.isOrdinal (maxω a b) ⟩
maxω-ordinal a b oa ob with lem (a ∈ˢ b)
... | inl⊎ _ = ob
... | inr⊎ _ = oa

maxω-in : (w a b : S) → ⟨ a ∈ˢ w ⟩ → ⟨ b ∈ˢ w ⟩
  → ⟨ maxω a b ∈ˢ w ⟩
maxω-in w a b ha hb with lem (a ∈ˢ b)
... | inl⊎ _ = hb
... | inr⊎ _ = ha

below-max : (a b x : S) → ⟨ x ∈ˢ maxω a b ⟩
  → ⟨ (x ∈ˢ a) ⊔ ((x ≈ˢ a) ⊔ ((x ∈ˢ b) ⊔ (x ≈ˢ b))) ⟩
below-max a b x hx with lem (a ∈ˢ b)
... | inl⊎ _ = ∣ inr⊎ ∣ inr⊎ ∣ inl⊎ hx ∣₁ ∣₁ ∣₁
... | inr⊎ _ = ∣ inl⊎ hx ∣₁
