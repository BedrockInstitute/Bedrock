{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.747] PROBE.  The uniform numeral leaf at a closed limit:
--
--   numeralL-in-carrier-lim :
--       (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
--       → ⟨ ω ∈ˢ γ ⟩
--       → (k : ℕ)
--       → ⟨ fst (numeralL k) ∈ˢ Lset γ ⟩
--
-- `Bound.num∈λ` (src/L/Coding/Bound.lagda.md:139-140) already places
-- `fst (numeralL k)` at `Lset lam` for an abstract limit `lam`; this probe
-- instantiates that module at `lam := γ` with
--   succλ := Closer.suc∈γ  (the 737-SPLIT closer, Probe737Split.agda
--                           :125-127, telescope trimmed, see below)
--   ∅∈λ   := oγ .fst (#∈ω zero) ω∈γ   (∅ ∈ ω ∈ γ by γ's transitivity;
--                           `# zero` reduces to `∅`, as Bound's own
--                           `#∈λ zero = ∅∈λ` clause witnesses)
-- Lands nothing in src/.  `table-sat` and `Sat-in-carrier-lim` are NOT
-- inhabited.  ONE deviation from the cited source, flagged at the Closer
-- module below.  [LJ-1.737]'s debt (i) consumes this leaf; the uniform
-- numeral bound it needs is exactly this statement.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-747.Probe747 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.Ordinal {ℓ} using ( mem-ord; #∈ω )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡ )
open import L.Ordinal.StageArith {ℓ} lem using ( +ω; +ω-mem; closedω )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Coding.Bound {ℓ} lem using ( module Bound )

open import Cubical.Data.Sum as Sum using ( _⊎_ )
import Cubical.Data.Empty as Empty
open import Cubical.Foundations.HLevels using ( isOfHLevelLift )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

------------------------------------------------------------------------------
-- SECTION 0.  The 737-SPLIT closer, verbatim from
-- agents/tasks/LJ-1-737-SPLIT/Probe737Split.agda:105-127 with ONE trim:
-- the `hγ : ⟨ isL γ ⟩` argument is dropped, because neither `no-succ` nor
-- `suc∈γ` mentions it (their bodies are unchanged token for token) and the
-- obligation of this probe does not carry `isL γ` in its telescope.  The
-- closer is transcribed rather than imported because an import of
-- Probe737Split would drag that whole probe frame into every check of
-- this one for an argument this file cannot supply; the same trade
-- Probe737Split itself records as its ONE DEVIATION.

module Closer (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ) where

  -- closedω forbids γ to be a successor:  γ = sucV x with x ∈ γ would
  -- put +ω x inside sucV x, and +ω x is neither below nor equal to x.
  no-succ : (x : V ℓ) → ⟨ x ∈ˢ γ ⟩ → sucV x ≡ γ → Empty.⊥
  no-succ x x∈ eq = lower
    (∈sucV-elim (isOfHLevelLift 1 Empty.isProp⊥) +ω∈sucx
      (λ h → lift (kA h)) (λ h → lift (k≡ h)))
    where
    ox : IsOrd x
    ox = mem-ord {A = γ} oγ x x∈
    +ω∈sucx : ⟨ +ω x ∈ˢ sucV x ⟩
    +ω∈sucx = subst (λ w → ⟨ +ω x ∈ˢ w ⟩) (sym eq) (clγ x x∈)
    kA : ⟨ +ω x ∈ˢ x ⟩ → Empty.⊥
    kA h = ∈-irrefl x (ox .fst (+ω-mem x) h)
    k≡ : +ω x ≡ x → Empty.⊥
    k≡ h≡ = ∈-irrefl x (subst (λ w → ⟨ x ∈ˢ w ⟩) h≡ (+ω-mem x))

  -- The strict successor step:  closedω makes every successor of a
  -- member a member.
  suc∈γ : (x : V ℓ) → ⟨ x ∈ˢ γ ⟩ → ⟨ sucV x ∈ˢ γ ⟩
  suc∈γ x x∈ = Sum.rec id (λ h → Empty.rec (no-succ x x∈ h))
    (suc∈or≡ x γ (mem-ord {A = γ} oγ x x∈) oγ x∈)

------------------------------------------------------------------------------
-- SECTION 1.  The carrier: `Bound` instantiated at `lam := γ`.  The two
-- arguments the brief names:  `succλ` is Section 0's `suc∈γ`;  `∅∈λ` is
-- `∅ ∈ ω ∈ γ`, the two legs the brief gives -- `#∈ω zero : ⟨ # zero ∈ˢ ω ⟩`
-- (src/L/Ordinal.lagda.md:248) with `# zero` reducing to `∅`, then the
-- transitivity half of `oγ` carries `∅` down to `γ` along `ω ∈ γ`.

module Carrier (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
               (ω∈γ : ⟨ ω ∈ˢ γ ⟩) where
  open Closer γ oγ clγ

  ∅∈λ : ⟨ ∅ ∈ˢ γ ⟩
  ∅∈λ = oγ .fst (#∈ω zero) ω∈γ

  module B = Bound γ oγ suc∈γ ∅∈λ

------------------------------------------------------------------------------
-- THE OBLIGATION.  Exported at the file's top level, at the name the
-- meter reads.  The body is the instantiation above, applied at its
-- telescope:  `B.num∈λ` already has exactly the obligation's type at
-- `lam := γ` (src/L/Coding/Bound.lagda.md:139).

numeralL-in-carrier-lim :
    (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
    → ⟨ ω ∈ˢ γ ⟩
    → (k : ℕ)
    → ⟨ fst (numeralL k) ∈ˢ Lset γ ⟩
numeralL-in-carrier-lim γ oγ clγ ω∈γ = Carrier.B.num∈λ γ oγ clγ ω∈γ
