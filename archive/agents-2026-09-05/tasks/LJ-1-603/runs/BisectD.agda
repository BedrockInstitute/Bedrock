{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.603]  BISECT ARM D.  The same index content as the record, but
-- spelled as a Sigma, with the projections named once.  Cut from
-- runs/W3.agda for the heap-wall bisection; see the report.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-603.runs.BisectD {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( Lset )
import L.StageCardinal

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )

module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq
open SC using ( _↪_ )

open Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪ )
open InfinitySet {ℓ} using ( ω; sucV )

InfStage : Type (ℓ-suc ℓ)
InfStage =
  Σ[ δ ∈ V ℓ ] Σ[ oδ ∈ IsOrd δ ] Σ[ δ∈suc ∈ ⟨ δ ∈ˢ sucV α₀ ⟩ ]
    Σ[ infδ ∈ (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) ] ⟨ ω ∈ˢ δ ⟩

δI : (i : InfStage) → V ℓ
δI i = fst i

oδI : (i : InfStage) → IsOrd (δI i)
oδI i = fst (snd i)

δ∈sucI : (i : InfStage) → ⟨ δI i ∈ˢ sucV α₀ ⟩
δ∈sucI i = fst (snd (snd i))

infδI : (i : InfStage) → (⟨ δI i ∈ˢ ω ⟩ → Empty.⊥)
infδI i = fst (snd (snd (snd i)))

ω∈δI : (i : InfStage) → ⟨ ω ∈ˢ δI i ⟩
ω∈δI i = snd (snd (snd (snd i)))

Ih : (i : InfStage) → Type ℓ
Ih i = (m : ⟪ δI i ⟫) → ⟪ Lset (⟪ δI i ⟫↪ m) ⟫ ↪ ⟪ δI i ⟫

step-fn : (i : InfStage) → Ih i → ⟪ Lset (δI i) ⟫ → ⟪ δI i ⟫
step-fn i ih =
  fst (SC.limit-step (δI i) (δ∈sucI i) (oδI i) (infδI i) ih)
