{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.117] probe A: the restricted sq at the site α = ω, machine-checked
-- against the restricted L.StageCardinal.
--
-- The restriction landed in the master: L.StageCardinal now takes the
-- site α₀ and sq : (δ : S) → δ ∈ sucV α₀ → (δ ∉ ω) → pairing δ.  At the
-- [LJ-1.94] site α₀ = ω the demand set is {ω} (lj-1.116 section 1), and
-- this probe supplies sqω from the honest ℕ pairing (pairω/pairω-inj,
-- src/ProbeLJ1106A.agda:127-137), instantiates the restricted module,
-- and checks the site's own stage-card-upper and the Bound count at ω.
--
-- Untracked probe; ONE agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty

module ProbeLJ1117A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open InfinitySet {ℓ} using ( ω; sucV )
open import FOL.Syntax using ( Formula )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim; self∈sucV )
open import L.Constructible {ℓ} using ( IsOrd; Lset; isPropIsOrd )
open import L.Ordinal {ℓ} using ( ω-ord; mem-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
import ProbeLJ1106A {ℓ} lem as P106
open P106 using ( module NumeralPresentation )
import L.StageCardinal

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

_↪_ : Type ℓ → Type ℓ → Type ℓ
X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)

pairing : S → Type ℓ
pairing δ = Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
              ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)

-- The honest pairing at ω: the demand at the site is satisfiable by
-- the delivered ℕ pairing, no Init, no truncation.
pairω : pairing ω
pairω = NumeralPresentation.pairω , NumeralPresentation.pairω-inj

-- The restricted supply at the site: sq at every δ ≤ ω (δ ∈ sucV ω),
-- with δ ∉ ω.  The only live case is δ = ω; a finite δ closes by inf,
-- and ω ∈ δ is refuted through the bound δ ∈ sucV ω.
sqω : (δ : S) → ⟨ δ ∈ sucV ω ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → pairing δ
sqω δ δ∈suc inf = go (ord-tri δ oδ ω ω-ord)
  where
  oδ : IsOrd δ
  oδ = ∈sucV-elim (isPropIsOrd δ) δ∈suc
    (λ δ∈ω → mem-ord {A = ω} ω-ord δ δ∈ω)
    (λ δ≡ω → subst IsOrd (sym δ≡ω) ω-ord)
  refute : ⟨ ω ∈ δ ⟩ → Empty.⊥
  refute ω∈δ = ∈-irrefl ω (∈sucV-elim (snd (ω ∈ ω)) δ∈suc
    (λ δ∈ω → ω-ord .fst {x = δ} {y = ω} ω∈δ δ∈ω)
    (λ δ≡ω → subst (λ w → ⟨ ω ∈ w ⟩) δ≡ω ω∈δ))
  go : ⟨ δ ∈ ω ⟩ ⊎ ((δ ≡ ω) ⊎ ⟨ ω ∈ δ ⟩) → pairing δ
  go (inl δ∈ω) = Empty.rec (inf δ∈ω)
  go (inr (inl δ≡ω)) = subst pairing (sym δ≡ω) pairω
  go (inr (inr ω∈δ)) = Empty.rec (refute ω∈δ)

-- The restricted module at the site, and the site's own checks.
module SC = L.StageCardinal {ℓ} lem ω ω-ord sqω
module Up = SC.Upper

up-ω : ⟪ Lset ω ⟫ ↪ ⟪ ω ⟫
up-ω = Up.stage-card-upper ω ω-ord (self∈sucV ω) (∈-irrefl ω)

module Bω = SC.Bound ω ω-ord (∈-irrefl ω) (sqω ω (self∈sucV ω) (∈-irrefl ω))

count-ω : (g : ⟪ Lset ω ⟫ ↪ ⟪ ω ⟫)
        → Σ[ f ∈ (Formula (⟪ Lset ω ⟫) 1 → ⟪ ω ⟫) ]
            ((φ ψ : Formula (⟪ Lset ω ⟫) 1) → f φ ≡ f ψ → φ ≡ ψ)
count-ω g = Bω.formula-bound {K = ⟪ Lset ω ⟫} g
