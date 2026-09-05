{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-299.Mini {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( fiber )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ} using ( ω-ord; #∈ω )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Cardinal {ℓ} lem using ( _↪_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω; #_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

-- GCH's SqShape body, verbatim (src/L/GCH.lagda.md:41-44).
SqShape : Type (ℓ-suc ℓ)
SqShape =
  (α : V ℓ) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
          → ⟪ α ⟫ × ⟪ α ⟫ ↪ ⟪ α ⟫

-- TEST A.  If the body parses as `⟪α⟫ × (⟪α⟫ ↪ ⟪α⟫)`, the second
-- projection is an injection of alpha into itself, and this checks.
testA : SqShape → (α : V ℓ) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
      → ⟪ α ⟫ ↪ ⟪ α ⟫
testA sq α oα h = sq α oα h .snd

-- TEST B.  An ordinal outside omega holds a member, by trichotomy.
mem : (α : V ℓ) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → ⟨ (# 0) ∈ˢ α ⟩
mem α oα nfin = go (ord-tri α oα ω (ω-ord))
  where
  go : (⟨ α ∈ˢ ω ⟩ ⊎ ((α ≡ ω) ⊎ ⟨ ω ∈ˢ α ⟩)) → ⟨ (# 0) ∈ˢ α ⟩
  go (inl a∈ω) = Empty.rec (nfin a∈ω)
  go (inr (inl e)) = subst (λ w → ⟨ (# 0) ∈ˢ w ⟩) (sym e) (#∈ω 0)
  go (inr (inr ω∈α)) = oα .fst (#∈ω 0) ω∈α

-- TEST C.  The parsed SqShape is provable outright: an element of the
-- carrier, paired with the identity self-injection.  The trophy's ONE
-- remaining hypothesis, as written today, gates nothing.
trivialSq : SqShape
trivialSq α oα nfin =
  (fiber α (mem α oα nfin) .fst , ((λ x → x) , (λ x y e → e)))
