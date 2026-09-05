{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.516] C-42 SWEEP.  A refutation measures ONE site.  This file
-- measures HOW FAR the shape extends, over the sixteen naming sites
-- [LJ-1.514] charged the 664 to (its table, lj-1.514-report.md:39-56).
-- The shape is "the formula carries no Δ₀ witness".  One line per site,
-- and Agda checks every one of them.  A site that IS Δ₀ makes its line
-- fail, so a green run is the whole count at once.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-516.runs.Sweep516 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.LevyHierarchy using ( Δ₀; δ-∧; δ-∨; δ-⇒; δ-¬; δ-∀∈; δ-∃∈ )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt; ApproxAt; StepAt )
open import L.Coding.Graph {ℓ} lem using ( satGraphAt )
open import L.Coding.Model {ℓ} using ( domAt; appAt; prAtL; tagAtL; closedAt )
open import L.Coding.Powerset {ℓ} lem
  using ( DefAt; DefinesAt; envOneAt; isCodeAt )
open import L.Coding.CodeSet {ℓ} lem using ( keyArityAtL; hasWitnessAt )
open import L.Coding.Shape {ℓ} using ( shapedAt )

module _ {n : ℕ} (w b : Fin n) where

  s04 : Δ₀ (domAt w b)         → ⊥* {ℓ}   -- Model:278
  s04 ()

  s01 : Δ₀ (LsetGraphAt w b)   → ⊥* {ℓ}   -- Sequence:291,349
  s01 ()
  s02 : Δ₀ (ApproxAt w b)      → ⊥* {ℓ}   -- Sequence:286
  s02 (δ-∧ _ ())
  s03 : Δ₀ (StepAt w b w)      → ⊥* {ℓ}   -- Sequence:119
  s03 (δ-∧ () _)
  s07 : Δ₀ (DefAt w b)         → ⊥* {ℓ}   -- Powerset:442
  s07 (δ-∧ () _)
  s08 : Δ₀ (isCodeAt w b)      → ⊥* {ℓ}   -- Powerset:297
  s08 (δ-∧ () _)
  s10 : Δ₀ (DefinesAt w b w)   → ⊥* {ℓ}   -- Powerset:217
  s10 (δ-∧ () _)
  s11 : Δ₀ (keyArityAtL w 1)   → ⊥* {ℓ}   -- CodeSet:135
  s11 ()
  s12 : Δ₀ (hasWitnessAt w b)  → ⊥* {ℓ}   -- CodeSet:240
  s12 ()
  s13 : Δ₀ (envOneAt w b)      → ⊥* {ℓ}   -- Powerset:128
  s13 (δ-∧ () _)
  s14 : Δ₀ (tagAtL w 0 b)      → ⊥* {ℓ}   -- Model:586, THE ROOT SITE
  s14 ()


