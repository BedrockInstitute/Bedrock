{-# OPTIONS --cubical --safe --guardedness #-}

-- [DD25 / LJ-1.41 REVIEW] THE CURE AT THE REAL ROW SITE.
--
-- ProbeDD25F41B proves the transfer for generic slots.  This probe
-- pins it at the Top row's own frame, E ∷ yc ∷ a ∷ ar ∷ c ∷ γ, which
-- is where the index bugs live, and it proves one more thing:
--
--   THE DELIVERED envHypT IS THE FIRST CONJUNCT OF THE CURE.
--
-- So the cure does not replace the story's environment hypothesis.
-- It adds the conjunct the story never wrote.  Everything already
-- proved about envHypT survives as `.fst`.
--
-- EXPECTED: GREEN.
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed; thrown away per D-1.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeDD25F41C {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Δ₀ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ} using ( envSetAt; envOverAt )
open import L.Condensation {ℓ} lem using ( envHypT; Δ₀-envHypT )
open import ProbeDD25F41B {ℓ} lem using ( envSetB; Δ₀-envSetB; module EnvSet )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- The Top row's frame is E ∷ yc ∷ a ∷ ar ∷ c ∷ γ.  E is slot 0, ar is
-- slot 3, and B and K sit 5 above their row slots.  These are the
-- machine's own indices at src/L/Coding/Model.lagda.md:1273 and
-- :1337.
module TopSite {m : ℕ} (B K : Fin m) where
  Eᵢ arᵢ Bᵢ Kᵢ : Fin (5 + m)
  Eᵢ  = zero
  arᵢ = suc (suc (suc zero))
  Bᵢ  = suc (suc (suc (suc (suc B))))
  Kᵢ  = suc (suc (suc (suc (suc K))))

  cure : Formula S (5 + m)
  cure = envSetB Eᵢ arᵢ Bᵢ Kᵢ

  -- The cure is Delta-0.
  Δ₀-cure : Δ₀ cure
  Δ₀-cure = Δ₀-envSetB Eᵢ arᵢ Bᵢ Kᵢ

  -- THE DELIVERED SHAPE SURVIVES.  The story's envHypT is conjunct
  -- one of the cure, definitionally.
  keeps-envHypT : (δ : S ^ (5 + m))
    → ⟨ δ ⊨ cure ⟩ → ⟨ δ ⊨ envHypT B K ⟩
  keeps-envHypT δ h = h .fst

  -- THE MACHINE'S OWN TYPE.  This is the hypothesis that
  -- topClause-out consumes at src/L/Coding/Model.lagda.md:1337.
  machine : Formula S (5 + m)
  machine = envSetAt Eᵢ arᵢ Bᵢ

  module Site (δ : S ^ (5 + m))
    (entryK : (z x y : S) → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
            → ⟨ fst x ∈ fst (lookup Kᵢ δ) ⟩ × ⟨ fst y ∈ fst (lookup Kᵢ δ) ⟩)
    (arSubK : (x : S) → ⟨ fst x ∈ fst (lookup arᵢ δ) ⟩
            → ⟨ fst x ∈ fst (lookup Kᵢ δ) ⟩)
    (envInK : (z : S) → ⟨ (z ∷ δ) ⊨ envOverAt zero (suc arᵢ) (suc Bᵢ) ⟩
            → ⟨ fst z ∈ fst (lookup Kᵢ δ) ⟩)
    where
    module T = EnvSet {5 + m} Eᵢ arᵢ Bᵢ Kᵢ δ entryK arSubK envInK

    -- STORY TO MACHINE: what the machine's clause demands.
    supply : ⟨ δ ⊨ cure ⟩ → ⟨ δ ⊨ machine ⟩
    supply = T.out

    -- MACHINE TO STORY: what the story's row demands.
    receive : ⟨ δ ⊨ machine ⟩ → ⟨ δ ⊨ cure ⟩
    receive = T.back
