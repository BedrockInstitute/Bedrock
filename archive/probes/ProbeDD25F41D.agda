{-# OPTIONS --cubical --safe --guardedness #-}

-- [DD25 / LJ-1.41 REVIEW] THE RED CONTROL.
--
-- ProbeDD25F41C reaches the machine's envSetAt from the two-conjunct
-- cure, under three site facts.  This control gives the SAME three
-- site facts and only the story's DELIVERED one-conjunct envHypT.
--
-- EXPECTED: RED.  If it were green, the cure's second conjunct would
-- be decoration and the site facts would be doing all the work.  A
-- red here isolates the missing conjunct as the whole difference, and
-- it CONFIRMS the [LJ-1.41] return's count: the nine rows as
-- delivered cannot close.
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed; thrown away per D-1.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeDD25F41D {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ} using ( envSetAt; envOverAt )
open import L.Condensation {ℓ} lem using ( envHypT )
open import ProbeDD25F41B {ℓ} lem using ( envSetB; module EnvSet )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

module Control {m : ℕ} (B K : Fin m) where
  Eᵢ arᵢ Bᵢ Kᵢ : Fin (5 + m)
  Eᵢ  = zero
  arᵢ = suc (suc (suc zero))
  Bᵢ  = suc (suc (suc (suc (suc B))))
  Kᵢ  = suc (suc (suc (suc (suc K))))

  module Site (δ : S ^ (5 + m))
    (entryK : (z x y : S) → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
            → ⟨ fst x ∈ fst (lookup Kᵢ δ) ⟩ × ⟨ fst y ∈ fst (lookup Kᵢ δ) ⟩)
    (arSubK : (x : S) → ⟨ fst x ∈ fst (lookup arᵢ δ) ⟩
            → ⟨ fst x ∈ fst (lookup Kᵢ δ) ⟩)
    (envInK : (z : S) → ⟨ (z ∷ δ) ⊨ envOverAt zero (suc arᵢ) (suc Bᵢ) ⟩
            → ⟨ fst z ∈ fst (lookup Kᵢ δ) ⟩)
    where
    module T = EnvSet {5 + m} Eᵢ arᵢ Bᵢ Kᵢ δ entryK arSubK envInK

    -- THE ATTEMPT.  The delivered one-conjunct hypothesis, and all
    -- three site facts.  Agda must refuse.
    supply : ⟨ δ ⊨ envHypT B K ⟩ → ⟨ δ ⊨ envSetAt Eᵢ arᵢ Bᵢ ⟩
    supply = T.out
