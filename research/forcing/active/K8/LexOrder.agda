{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.LexOrder
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (sep : OrdinaryProfile.Separation 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _≐_; _∧̇_; _∨̇_ )
import CardinalBridge
import K8.OmegaMax
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
module CB = CardinalBridge 𝒮
module OM = K8.OmegaMax 𝒮 ext paths sep find lem
open OM using ( module CO; ≈→≡ )

Lex : S → S → Ω → Ω
Lex a b R = (a ∈ˢ b) ⊔ ((a ≈ˢ b) ⊓ R)

lexAt : ∀ {n} → Fin n → Fin n → Formula S n → Formula S n
lexAt a b R = (var a ∈̇ var b) ∨̇ ((var a ≐ var b) ∧̇ R)

lex-irrefl : (a : S) (R : Ω) → (⟨ R ⟩ → Empty.⊥)
  → ⟨ Lex a a R ⟩ → Empty.⊥
lex-irrefl a R noR = PT.rec Empty.isProp⊥ λ
  { (inl aa) → CO.no-self find a aa ; (inr (_ , r)) → noR r }

lex-trans : (a b c : S) (R T U : Ω) → ⟨ CB.isOrdinal c ⟩
  → (⟨ R ⟩ → ⟨ T ⟩ → ⟨ U ⟩)
  → ⟨ Lex a b R ⟩ → ⟨ Lex b c T ⟩ → ⟨ Lex a c U ⟩
lex-trans a b c R T U oc rt = PT.rec (isPropΠ (λ _ → snd (Lex a c U))) first
  where
  first : ⟨ a ∈ˢ b ⟩ ⊎ ⟨ (a ≈ˢ b) ⊓ R ⟩
    → ⟨ Lex b c T ⟩ → ⟨ Lex a c U ⟩
  first (inl ab) = PT.rec (snd (Lex a c U)) λ
    { (inl bc) → ∣ inl (oc .fst b bc a ab) ∣₁
    ; (inr (eq , _)) → ∣ inl (subst (λ z → ⟨ a ∈ˢ z ⟩) (≈→≡ eq) ab) ∣₁ }
  first (inr (eq , r)) = PT.rec (snd (Lex a c U)) λ
    { (inl bc) → ∣ inl (subst (λ z → ⟨ z ∈ˢ c ⟩) (sym (≈→≡ eq)) bc) ∣₁
    ; (inr (eq' , t)) → ∣ inr (CO.≈-trans a b c eq eq' , rt r t) ∣₁ }

lex-compare : (a b : S) (R E T : Ω)
  → ⟨ CB.isOrdinal a ⟩ → ⟨ CB.isOrdinal b ⟩
  → ⟨ R ⊔ (E ⊔ T) ⟩
  → ⟨ Lex a b R ⊔ (((a ≈ˢ b) ⊓ E) ⊔ Lex b a T) ⟩
lex-compare a b R E T oa ob rest = PT.rec (snd goal) first
  (CO.ord-compare find sep lem a b oa ob)
  where
  goal : Ω
  goal = Lex a b R ⊔ (((a ≈ˢ b) ⊓ E) ⊔ Lex b a T)
  first : ⟨ a ∈ˢ b ⟩ ⊎ ⟨ (a ≈ˢ b) ⊔ (b ∈ˢ a) ⟩ → ⟨ goal ⟩
  first (inl ab) = ∣ inl ∣ inl ab ∣₁ ∣₁
  first (inr more) = PT.rec (snd goal) (λ
    { (inr ba) → ∣ inr ∣ inr ∣ inl ba ∣₁ ∣₁ ∣₁
    ; (inl eq) → PT.rec (snd goal) (λ
        { (inl r) → ∣ inl ∣ inr (eq , r) ∣₁ ∣₁
        ; (inr last) → PT.rec (snd goal) (λ
            { (inl e) → ∣ inr ∣ inl (eq , e) ∣₁ ∣₁
            ; (inr t) → ∣ inr ∣ inr ∣ inr (CO.≈-sym a b eq , t) ∣₁ ∣₁ ∣₁ }) last }) rest }) more
