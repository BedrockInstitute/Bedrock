{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.594]  W3.  THE WIDEST UNMEASURED TERM: `L.StageCardinal`'s `sq`
-- PARAMETER, RE-ASCRIBED ALONE.  TYPE ONLY.
--
-- The brief names it: "It is `sq`'s type at the module header", and it
-- orders this file written FIRST and typechecked ALONE.
--
-- `SqParam` is transcribed from src/L/StageCardinal.lagda.md:17-20 and
-- NOTHING ELSE IS IN THIS FILE except the one row that proves the
-- transcription is right: `L.StageCardinal` accepts a `SqParam α₀` as
-- its own parameter.  If the transcription drifted by one character the
-- module application below would not elaborate.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

module LJ-1-594.runs.W3 {ℓ : Level} where

open import Cubical.Data.Sigma using ( _×_ )
import L.StageCardinal

-- W3.1  THE TYPE, ALONE.  src/L/StageCardinal.lagda.md:17-20.
SqParam : V ℓ → Type (ℓ-suc ℓ)
SqParam α₀ =
  (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
    → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
        ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)

-- W3.2  AND IT IS THE MODULE'S OWN PARAMETER, not a paraphrase of it.
--       The application elaborates only if the two types agree.
module _ (lem : LEM (ℓ-suc ℓ)) (α₀ : V ℓ) (oα₀ : IsOrd α₀) (sq : SqParam α₀) where
  module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq

-- W3.3  WHAT IT CARRIES, READ OFF THE TYPE.  One function on the pairs
--       of the members of δ, and one injectivity proof of it.  NO
--       `Formula`, no L-set, no satisfaction, no ordinal grade.  The
--       two projections below are the whole content of the parameter.
pairing-part : (α₀ : V ℓ) → SqParam α₀ → (δ : V ℓ)
             → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
             → (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫)
pairing-part α₀ sq δ d∈ d∉ = fst (sq δ d∈ d∉)

inj-part : (α₀ : V ℓ) (sq : SqParam α₀) (δ : V ℓ)
           (d∈ : ⟨ δ ∈ InfinitySet.sucV α₀ ⟩) (d∉ : ⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
         → (x y : ⟪ δ ⟫ × ⟪ δ ⟫)
         → pairing-part α₀ sq δ d∈ d∉ x ≡ pairing-part α₀ sq δ d∈ d∉ y → x ≡ y
inj-part α₀ sq δ d∈ d∉ = snd (sq δ d∈ d∉)
