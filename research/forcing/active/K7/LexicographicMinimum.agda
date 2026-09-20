{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K7.LexicographicMinimum {ℓ}
  (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (sep : OrdinaryProfile.Separation 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (lem : LEM ℓ) (d : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; con; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import Cubical.Data.Sum using ( inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
import GroundDescription
import CodedVocabulary

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )
open PT using ( ∣_∣₁ )
module Ground = GroundDescription 𝒮 ext paths
module Code = CodedVocabulary 𝒮

Bounded : ∀ {n} → Vec S n → Ω
Bounded [] = ⊤
Bounded (x ∷ ν) = (x ∈ˢ d) ⊓ Bounded ν

Equal : ∀ {n} → Vec S n → Vec S n → Ω
Equal [] [] = ⊤
Equal (x ∷ ν) (y ∷ μ) = (x ≈ˢ y) ⊓ Equal ν μ

equal-path : ∀ {n} (ν μ : Vec S n) → ⟨ Equal ν μ ⟩ → ν ≡ μ
equal-path [] [] h = refl
equal-path (x ∷ ν) (y ∷ μ) (e , h) =
  cong₂ _∷_ (subst ⟨_⟩ (paths x y) e) (equal-path ν μ h)

ReverseLex : ∀ {n} → Vec S n → Vec S n → Ω
ReverseLex [] [] = ⊥
ReverseLex (x ∷ ν) (y ∷ μ) = ReverseLex ν μ ⊔ (Equal ν μ ⊓ (x ∈ˢ y))

Witness : ∀ {n} → Formula S n → Vec S n → Ω
Witness φ ν = Bounded ν ⊓ (ν ⊨ φ)

Minimum : ∀ {n} → Formula S n → Vec S n → Ω
Minimum {n} φ ν = Witness φ ν ⊓
  ⋀ (Vec S n) (λ μ → Witness φ μ ⇒ (ReverseLex μ ν ⇒ ⊥))

minimum : (n : ℕ) (φ : Formula S n)
  → ⟨ ⋁ (Vec S n) (Witness φ) ⟩ → ⟨ ⋁ (Vec S n) (Minimum φ) ⟩
minimum zero φ = PT.map (λ { ([] , h) → [] , h , λ { [] _ less → less } })
minimum (suc n) φ inhabited = PT.rec (snd target) atTail
  (minimum n (∃̇∈ (con d) φ)
    (PT.map (λ { (x ∷ ν , (hx , hν) , sat) → ν , hν , ∣ x , hx , sat ∣₁ }) inhabited))
  where
  target : Ω
  target = ⋁ (Vec S (suc n)) (Minimum φ)

  atTail : Σ[ ν ∈ Vec S n ] ⟨ Minimum (∃̇∈ (con d) φ) ν ⟩ → ⟨ target ⟩
  atTail (ν , (hν , some) , leastTail) = PT.map atHead
    (OrdinaryProfile.foundation→minimal 𝒮 find lem candidates
      (PT.map (λ { (x , hx , sat) → x , candidate-in x hx sat }) some))
    where
    candidates : S
    candidates = Ground.separateOf sep d (Code.sepAt φ ν)

    candidate-in : (x : S) → ⟨ x ∈ˢ d ⟩ → ⟨ (x ∷ ν) ⊨ φ ⟩
      → ⟨ x ∈ˢ candidates ⟩
    candidate-in x hx sat = subst ⟨_⟩
      (sym (Ground.separateOf-spec sep d (Code.sepAt φ ν) x))
      (hx , subst ⟨_⟩ (sym (Code.sepAt-reading φ ν x)) sat)

    candidate-out : (x : S) → ⟨ x ∈ˢ candidates ⟩
      → ⟨ (x ∈ˢ d) ⊓ ((x ∷ ν) ⊨ φ) ⟩
    candidate-out x hx = fst read , subst ⟨_⟩ (Code.sepAt-reading φ ν x) (snd read)
      where
      read = subst ⟨_⟩ (Ground.separateOf-spec sep d (Code.sepAt φ ν) x) hx

    atHead : Σ[ x ∈ S ] ⟨ (x ∈ˢ candidates) ⊓
      ⋀ S (λ y → ((y ∈ˢ x) ⊓ (y ∈ˢ candidates)) ⇒ ⊥) ⟩
      → Σ[ μ ∈ Vec S (suc n) ] ⟨ Minimum φ μ ⟩
    atHead (x , hx , leastHead) = (x ∷ ν) , ((fst read , hν) , snd read) , smaller
      where
      read = candidate-out x hx

      smaller : (μ : Vec S (suc n)) → ⟨ Witness φ μ ⟩
        → ⟨ ReverseLex μ (x ∷ ν) ⟩ → ⟨ ⊥ ⟩
      smaller (y ∷ μ) ((hy , hμ) , sat) = PT.rec (snd ⊥) λ
        { (inl less) → leastTail μ (hμ , ∣ y , hy , sat ∣₁) less
        ; (inr (eq , less)) → leastHead y (less , candidate-in y hy
            (subst (λ ρ → ⟨ (y ∷ ρ) ⊨ φ ⟩) (equal-path μ ν eq) sat)) }
