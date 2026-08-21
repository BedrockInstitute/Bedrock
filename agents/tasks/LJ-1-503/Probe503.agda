{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.503] Which omega gate wins, settled at the one site that
-- consumes it.
--
-- W3 FIRST, and ALONE: the implication between the two gates.
--
--   gam-to-sucV : ⟨ ω ∈ gam ⟩ → ⟨ ω ∈ sucV gam ⟩
--
-- [LJ-1.491] asserted this in prose
-- (agents/tasks/LJ-1-491/lj-1.491-report.md:246: "The stronger
-- gate excludes `gam = ω`").  Nothing built it.  If it does not
-- typecheck the two gates are not comparable and the question
-- changes shape.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-503.Probe503 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV; ω )
open import V.Model {ℓ} using ( ∈sucV-inl )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

-- =====================================================================
-- W3.  THE IMPLICATION BETWEEN THE TWO GATES.
--
--   KValue's gate       ⟨ ω ∈ gam ⟩          [LJ-1.491], GO
--   SupplyEnv's gate    ⟨ ω ∈ sucV gam ⟩     src/L/Coding/EnvSupply.lagda.md:111
--
-- `∈sucV-inl` (src/V/Model.lagda.md:230) is stated at 𝒮ᵥ, whose
-- `_∈ˢ_` field IS Cubical's `_∈_` (src/V/Hierarchy.lagda.md:83), so
-- the two memberships are the same relation and no reshaping is
-- needed.  `ω` and `gam` are both `V ℓ`.
-- =====================================================================

gam-to-sucV : (gam : V ℓ) → ⟨ ω ∈ gam ⟩ → ⟨ ω ∈ sucV gam ⟩
gam-to-sucV gam ω∈γ = ∈sucV-inl {A = gam} {x = ω} ω∈γ

-- =====================================================================
-- D-10, SETTLED BEFORE THE OBLIGATION WAS BUILT.
--
-- The brief asks which gate `envSetNumeral∈` asks for.  It asks for
-- NEITHER candidate literally.  Its signature is
--
--   envSetNumeral∈ : (σ : V ℓ) → IsOrd σ → ⟨ ω ∈ σ ⟩ → ...
--                                          ^^^^^^^^^
--   src/L/Coding/Key.lagda.md:486
--
-- so the gate is a hypothesis about its OWN first argument and not
-- about `gam` at all.  The site fixes that argument.  In `envSetK`
-- the argument is `σ = sucV gam` (src/L/Coding/EnvSupply.lagda.md:115-116
-- for the abbreviation, :146 for the application), and `σ` is not
-- free there: `B₀∈σ : ⟨ fst B₀ ∈ Lset σ ⟩` is proved through
-- `Lset-suc gam` (:128), which pins `σ` to `sucV gam`.  So the gate
-- the ONE consumer asks for is exactly `⟨ ω ∈ sucV gam ⟩`, which is
-- SupplyEnv's own hypothesis, verbatim.
--
-- That makes `⟨ ω ∈ sucV gam ⟩` the WEAKEST SUFFICIENT hypothesis at
-- this site, and the brief's own rule then applies: the weakest
-- sufficient hypothesis is the right answer.  It does not make the
-- stronger gate unusable, and the obligation below settles that
-- separately by BUILDING `envSetK` from `⟨ ω ∈ gam ⟩` alone.

open import L.Constructible {ℓ}
  using ( isL; isL-trans; Lset; IsOrd; Lset-mono; 𝒟ₒ-intro )
open import L.Axioms.Basic {ℓ} using ( LsetS; Lset-suc )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.StageArith {ℓ} lem using ( sucIter )
open import L.Coding.Bound {ℓ} lem using ( module Bound )
open import L.Coding.Key {ℓ} lem using ( envSetNumeral∈ )
open import L.Coding.Sound {ℓ} lem using ( module NumeralFromGeneric )
open import L.Coding.EnvSet {ℓ} lem using ( envSet; module Generic )
open import FOL.Syntax using ( ⊤̇ )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ∅ )
open InfinitySet {ℓ} using ( #_ )
open import Cubical.HITs.PropositionalTruncation using ( ∣_∣₁ )

-- =====================================================================
-- THE FRAME.  SupplyEnv's telescope (src/L/Coding/EnvSupply.lagda.md
-- :107-111) with ONE substitution: the last hypothesis is KValue's
-- gate `⟨ ω ∈ gam ⟩` ([LJ-1.491], GO at
-- agents/tasks/LJ-1-491/lj-1.491-report.md:76) in place of
-- SupplyEnv's `⟨ ω ∈ sucV gam ⟩`.
--
-- The first seven binders are KValue's own telescope verbatim
-- (src/L/Condensation.lagda.md:7380), so this frame IS KValue's
-- frame under [LJ-1.491]'s restriction, and nothing extra is
-- hypothesised.  REBUILT, not patched: SupplyEnv is never
-- instantiated below, `src/` is untouched, and no probe is imported.
-- =====================================================================

module Frame
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  (ω∈γ : ⟨ ω ∈ gam ⟩) where

  module B = Bound lam ordλ succλ ∅∈λ

  -- The one place the substitution is paid for: W3 turns KValue's
  -- gate into the gate the consumer asks for.  Everything after this
  -- line is SupplyEnv's own text.
  ω∈σ : ⟨ ω ∈ sucV gam ⟩
  ω∈σ = gam-to-sucV gam ω∈γ

  σ : V ℓ
  σ = sucV gam

  oσ : IsOrd σ
  oσ = suc-ord ordγ

  σ∈λ : ⟨ σ ∈ lam ⟩
  σ∈λ = succλ gam γ∈λ

  B₀ : S
  B₀ = LsetS gam ordγ

  B₀∈σ : ⟨ fst B₀ ∈ Lset σ ⟩
  B₀∈σ = subst (λ w → ⟨ Lset gam ∈ w ⟩) (sym (Lset-suc gam))
    (𝒟ₒ-intro (Lset gam) (Lset gam) ∣ ⊤̇ , DefA.defSet⊤≡A ∣₁)
    where
    module DefA = DefOf (Lset gam)

  genEq : (ar : S) (n : ℕ) → fst ar ≡ # n
        → fst (Generic.envSetGen B₀ ar) ≡ fst (envSet B₀ n)
  genEq ar n arNum =
    cong (λ ar' → fst (Generic.envSetGen B₀ ar'))
      (Σ≡Prop (λ x → (isL x) .snd) arNum)
    ∙ sym (NumeralFromGeneric.derived B₀ n)

  -- THE CONCLUSION IS SupplyEnv's, UNWEAKENED
  -- (src/L/Coding/EnvSupply.lagda.md:140-146).  Not one hypothesis
  -- was added and not one conclusion was cut back.
  envSetK : (ar : S) (n : ℕ) → fst ar ≡ # n
          → ⟨ fst ar ∈ Lset lam ⟩
          → ⟨ fst (Generic.envSetGen B₀ ar) ∈ Lset lam ⟩
  envSetK ar n arNum ar∈λ =
    Lset-mono {α = lam} {β = sucIter 4 σ} (B.suc^∈λ 4 σ σ∈λ)
      (subst (λ w → ⟨ w ∈ Lset (sucIter 4 σ) ⟩) (sym (genEq ar n arNum))
        (envSetNumeral∈ σ oσ ω∈σ B₀ n B₀∈σ))

-- =====================================================================
-- THE OBLIGATION.
-- =====================================================================

envSetK-at-KValue-gate :
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  (ω∈γ : ⟨ ω ∈ gam ⟩)
  (ar : S) (n : ℕ) → fst ar ≡ # n
  → ⟨ fst ar ∈ Lset lam ⟩
  → ⟨ fst (Generic.envSetGen (LsetS gam ordγ) ar) ∈ Lset lam ⟩
envSetK-at-KValue-gate lam ordλ succλ ∅∈λ gam ordγ γ∈λ ω∈γ =
  Frame.envSetK lam ordλ succλ ∅∈λ gam ordγ γ∈λ ω∈γ

-- =====================================================================
-- THE GAP BETWEEN THE TWO GATES, MEASURED AND NOT ASSERTED.
--
-- W3 gives one inclusion.  These two terms give the other side, so
-- the relation between the gates is BUILT and no part of it stays in
-- prose:
--
--   `sucV-gate-splits` : SupplyEnv's gate IS the disjunction
--                        "ω ∈ gam  or  ω ≡ gam".
--   `gam≡ω-drives`     : the second disjunct alone already drives it.
--
-- Together with `gam-to-sucV` this says the two gates differ by
-- EXACTLY the case `gam ≡ ω`, and that SupplyEnv's gate admits that
-- case while KValue's cannot.  So SupplyEnv's gate is the strictly
-- weaker of the two, and it is the one the consumer asks for.
-- =====================================================================

open import V.Model {ℓ} using ( ∈sucV-elim; self∈sucV )
import Cubical.Data.Sum as Sum
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

sucV-gate-splits : (gam : V ℓ) → ⟨ ω ∈ sucV gam ⟩
                 → ∥ ⟨ ω ∈ gam ⟩ Sum.⊎ (ω ≡ gam) ∥₁
sucV-gate-splits gam h =
  ∈sucV-elim {A = gam} {x = ω} PT.isPropPropTrunc h
    (λ ω∈g → ∣ Sum.inl ω∈g ∣₁)
    (λ q → ∣ Sum.inr q ∣₁)

gam≡ω-drives : (gam : V ℓ) → gam ≡ ω → ⟨ ω ∈ sucV gam ⟩
gam≡ω-drives gam q = subst (λ w → ⟨ ω ∈ sucV w ⟩) (sym q) (self∈sucV ω)
