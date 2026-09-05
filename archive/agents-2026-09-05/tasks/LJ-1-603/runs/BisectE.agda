{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.603]  BISECT ARM E.  Row 1.7 alone, stated against the frame,
-- to read its type error without paying the P601 import.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-603.runs.BisectE {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

open import FOL.Syntax using ( Formula )
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Count {ℓ} using ( code )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
import L.StageCardinal

open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Vec using ( Vec )
open InfinitySet {ℓ} using ( ω; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq

count-bound-is-sq-packs :
    (δ : V ℓ) (oδ : IsOrd δ) (δ∈suc : ⟨ δ ∈ˢ sucV α₀ ⟩)
    (infδ : ⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
    {K : Type ℓ}
    (g : Σ[ f ∈ (K → ⟪ δ ⟫) ] ((x y : K) → f x ≡ f y → x ≡ y))
    (k : ℕ) (ψ : Formula (⊥* {ℓ}) k) (n : ℕ) (cs : Vec K k)
  → SC.Bound.count-bound δ oδ infδ (sq δ δ∈suc infδ) g (k , (ψ , (n , cs)))
    ≡ SC.Bound.pair δ oδ infδ (sq δ δ∈suc infδ)
         (SC.Bound.numeral δ oδ infδ (sq δ δ∈suc infδ) k)
         (SC.Bound.pair δ oδ infδ (sq δ δ∈suc infδ)
           (SC.Bound.pair δ oδ infδ (sq δ δ∈suc infδ)
             (SC.Bound.numeral δ oδ infδ (sq δ δ∈suc infδ) (code ψ))
             (SC.Bound.numeral δ oδ infδ (sq δ δ∈suc infδ) n))
           (SC.Bound.tuple-g δ oδ infδ (sq δ δ∈suc infδ) g k cs))
count-bound-is-sq-packs _ _ _ _ _ _ _ _ _ = refl
