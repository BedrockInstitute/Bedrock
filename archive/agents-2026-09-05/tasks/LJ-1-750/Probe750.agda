{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.750] PROBE.  The tag-atom leaf at a closed limit:  a numeral code
-- paired with a stage member of Lset γ.
--
--   prʟ-numeral-in-Lset-lim :
--       (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
--       → ⟨ ω ∈ˢ γ ⟩
--       (k : ℕ) (a : S)
--       → ⟨ fst a ∈ˢ Lset γ ⟩
--       → ⟨ fst (prʟ (numeralL k) a) ∈ˢ Lset γ ⟩
--
-- This is W3's composition term, not a second numeral bound:  747's
-- numeralL-in-carrier-lim (agents/tasks/LJ-1-747/Probe747.agda:111)
-- supplies `fst (numeralL k) ∈ˢ Lset γ`, 749's prʟ-in-Lset-lim
-- (agents/tasks/LJ-1-749/Probe749.agda:57) lifts any two stage members'
-- V-pair into the code presentation, and the obligation is their
-- application at first argument `numeralL k`.  Both predecessor probes
-- delivered GO (lj-1.747-report.md, lj-1.749-report.md), so the type is
-- the type those probes typechecked, per the coder clause.
--
-- NOT inhabited here:  `table-sat` and `Sat-in-carrier-lim` (the brief
-- forbids both).  Lands nothing in src/.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and untouched here.

open import Base.Prelude
open import Base.Classical using ( LEM )

module LJ-1-750.Probe750 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω )
open import L.Constructible {ℓ} using ( IsOrd; Lset; 𝒮ʟ )
open import L.Ordinal.StageArith {ℓ} lem using ( closedω )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Coding.Model {ℓ} using ( prʟ )
open import LJ-1-747.Probe747 {ℓ} lem using ( numeralL-in-carrier-lim )
open import LJ-1-749.Probe749 {ℓ} lem using ( prʟ-in-Lset-lim )

-- The V open supplies ∈ˢ at V (the statement's membership); its own S
-- (= V ℓ) is hidden so that the L carrier S (𝒮ʟ's Σ over isL) is the
-- unambiguous S the obligation reads, exactly as 749's probe does.
open hPropStructure 𝒮ᵥ hiding ( S )
open hPropStructure 𝒮ʟ using ( S )

------------------------------------------------------------------------------
-- THE OBLIGATION.  Exported at the file's top level, at the name the
-- meter reads.  749's leaf at `a := numeralL k`, `b := a`; its first
-- membership argument is 747's leaf at `k`.  Nothing else enters.

-- Statement note:  the brief's text joins `(k : ℕ) (a : S)` to the ω
-- hypothesis with no arrow, which does not parse as Agda; the repair is
-- one arrow per premise, the exact shape 747's delivered obligation has
-- (`→ ⟨ ω ∈ˢ γ ⟩ → (k : ℕ) → ...`).  Argument order and content are the
-- brief's own:  γ oγ clγ, ω ∈ γ, then k, a, and the membership of fst a.
prʟ-numeral-in-Lset-lim :
    (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
    → ⟨ ω ∈ˢ γ ⟩
    → (k : ℕ) → (a : S)
    → ⟨ fst a ∈ˢ Lset γ ⟩
    → ⟨ fst (prʟ (numeralL k) a) ∈ˢ Lset γ ⟩
prʟ-numeral-in-Lset-lim γ oγ clγ ω∈γ k a ha =
  prʟ-in-Lset-lim γ oγ clγ (numeralL k) a
    (numeralL-in-carrier-lim γ oγ clγ ω∈γ k) ha
