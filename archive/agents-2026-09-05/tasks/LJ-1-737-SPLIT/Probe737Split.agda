{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.737-SPLIT] PROBE.  pair-in-Lγω at the top-level name the meter
-- reads:  [LJ-1.737]'s delivered term (agents/tasks/LJ-1-737/
-- Probe737.agda:115-117) with Underω's telescope as leading arguments.
-- Lands nothing in src/.
--
--   THE OBLIGATION   pair-in-Lγω.  INHABITED at the file's end.
--   NOT DELIVERED    table-sat.  Two tree debts block the satisfaction
--                    (lj-1.737-report.md, debts (i) and (ii)); neither is
--                    this obligation.
--   SHAPE            Closer's no-succ/suc∈γ and the Underω module are
--                    verbatim transcriptions; iter∈γ and block∈Lγ are
--                    trimmed, because they served the table-sat route,
--                    which this file does not name.
--   ONE DEVIATION    Frame.pair-in-Lγ is INLINED from [LJ-1.724-SPLIT]
--                    (Probe724Split.agda, module Frame) instead of
--                    imported.  The import would drag the 698/693/520
--                    probe chain into every check, and on 2026-08-29
--                    05:24-05:41 the box's agda-watchdog killed every
--                    agda process within one sweep while system swap sat
--                    at 8758 MB (_build/tools/agda-watchdog.log), so the
--                    cold chain could never land its interfaces.  The
--                    inlined leg is verbatim and rests on src/ chapters
--                    only, which are warm.  W2 note: the leg is now
--                    written twice in the tree; the canonical home stays
--                    the 724-SPLIT probe, and a later chapter-sized
--                    placement leg should absorb it.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-737-SPLIT.Probe737Split {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.Syntax using ( ⊤̇ )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Coding {ℓ} using ( pr )
open import V.Model {ℓ} using ( ∈sucV-elim )
open import L.Constructible {ℓ}
  using ( isL; IsOrd; Lset; Lset-mono; 𝒟ₒ-intro )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem
  using ( suc∈or≡; ord∈Lset-suc )
open import L.Ordinal.StageArith {ℓ} lem
  using ( +ω; +ω-mem; closedω )
open import L.Axioms.Basic {ℓ} using ( Lset-suc; pr∈Lset-suc )
open import L.Definability {ℓ} using ( module DefOf )
open import Cubical.Data.Sum as Sum using ( _⊎_ )
import Cubical.Data.Empty as Empty
open import Cubical.Foundations.HLevels using ( isOfHLevelLift )
open import Cubical.HITs.PropositionalTruncation using ( ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

------------------------------------------------------------------------------
-- SECTION 0.  The breadth leg, inlined verbatim from [LJ-1.724-SPLIT]'s
-- Frame (Probe724Split.agda), trimmed to what pair-in-Lγ reaches.

module Frameγ (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩) where

  -- A stage is its own definable subset, hence sits in the next stage
  -- (src/L/Axioms/Basic.lagda.md:196, src/L/Definability.lagda.md:178).
  Lset-self : (δ : V ℓ) → ⟨ Lset δ ∈ˢ Lset (sucV δ) ⟩
  Lset-self δ =
    subst (λ w → ⟨ Lset δ ∈ˢ w ⟩) (sym (Lset-suc δ))
      (𝒟ₒ-intro (Lset δ) (Lset δ) ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset δ) ∣₁)

  -- The pair's rank is x+2 at the top, so the scope x+2 in gamma places
  -- pr x (Lset x) in Lset gamma.  suc∈or≡ splits at suc^3 x:  past it,
  -- monotonicity carries the leg;  at it, the goal is pair∈Lx3's own
  -- stage and one transport along eq lands it.  The implicits of
  -- Lset-mono are named:  left to inference under Sum.rec they send the
  -- unifier into the sucV encodings (724-SPLIT header, REPAIRED).
  pair-in-Lγ : (x : V ℓ) (ox : IsOrd x)
             (hx2 : ⟨ sucV (sucV x) ∈ˢ γ ⟩)
           → ⟨ pr x (Lset x) ∈ˢ Lset γ ⟩
  pair-in-Lγ x ox hx2 =
    Sum.rec (λ x3∈γ →
              Lset-mono {γ} {sucV (sucV (sucV x))} x3∈γ {pr x (Lset x)}
                (pair∈Lx3 x ox))
            (λ eq →
              subst (λ w → ⟨ pr x (Lset x) ∈ˢ Lset w ⟩) eq (pair∈Lx3 x ox))
            (suc∈or≡ (sucV (sucV x)) γ (suc-ord (suc-ord ox)) oγ hx2)
    where
    pair∈Lx3 : (x : V ℓ) (ox : IsOrd x)
             → ⟨ pr x (Lset x) ∈ˢ Lset (sucV (sucV (sucV x))) ⟩
    pair∈Lx3 x ox = pr∈Lset-suc (sucV x) x (Lset x)
                      (ord∈Lset-suc x ox) (Lset-self x)

------------------------------------------------------------------------------
-- SECTION 1.  closedω arithmetic, the legs the pair placement stands on.
-- Verbatim from [LJ-1.737]'s Closer (Probe737.agda:41-68), trimmed to
-- what pair-in-Lγω reaches.

module Closer (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩) (clγ : closedω γ) where

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
-- SECTION 2.  The conclusion-side placement under closedω.  [LJ-1.724-
-- SPLIT] placed pr x (Lset x) in Lset γ only at the scope x+2 < γ;
-- closedω derives that iterate membership, so the placement holds for
-- EVERY member x.  Frameγ's pair-in-Lγ is the breadth leg.

module Underω (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩) (clγ : closedω γ) where

  open Closer γ oγ hγ clγ
  open Frameγ γ oγ hγ

  x²∈γ : (x : V ℓ) → ⟨ x ∈ˢ γ ⟩ → ⟨ sucV (sucV x) ∈ˢ γ ⟩
  x²∈γ x x∈ = suc∈γ (sucV x) (suc∈γ x x∈)

  pair-in-Lγω : (x : V ℓ) → ⟨ x ∈ˢ γ ⟩ → ⟨ pr x (Lset x) ∈ˢ Lset γ ⟩
  pair-in-Lγω x x∈ =
    pair-in-Lγ x (mem-ord {A = γ} oγ x x∈) (x²∈γ x x∈)

------------------------------------------------------------------------------
-- THE OBLIGATION.  The delivered term at the top-level name the meter
-- reads:  Underω's telescope as leading arguments.

pair-in-Lγω :
    (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩) (clγ : closedω γ)
    (x : V ℓ) → ⟨ x ∈ˢ γ ⟩ → ⟨ pr x (Lset x) ∈ˢ Lset γ ⟩
pair-in-Lγω γ oγ hγ clγ = Underω.pair-in-Lγω γ oγ hγ clγ
