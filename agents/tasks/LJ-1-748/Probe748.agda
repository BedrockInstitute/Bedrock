{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.748] PROBE.  pr-in-Lset-lim at the top-level name the brief
-- names:  BoundOver.pr∈λ (src/L/Coding/Bound.lagda.md:69-91) instantiated
-- at T := Lset, lam := γ, under the closedω telescope (γ oγ clγ).
-- Lands nothing in src/.
--
--   THE OBLIGATION   pr-in-Lset-lim.  Pairing of TWO STAGE MEMBERS,
--                    x, y ∈ˢ Lset γ.  This is NOT pair-in-Lγω, which
--                    places pr x (Lset x) for x ∈ γ
--                    (agents/tasks/LJ-1-737-SPLIT/Probe737Split.agda:151).
--   NOT DELIVERED    table-sat, pair-in-Lγω.  Neither name occurs here.
--   SHAPE            Closer's no-succ/suc∈γ are verbatim from
--                    [LJ-1.737-SPLIT] (Probe737Split.agda:106-127) with
--                    the hγ argument DROPPED:  neither leg reads it.
--   ONE DEVIATION    The src wrapper `Bound` (src/L/Coding/Bound.lagda.md:
--                    132-139) demands ∅∈λ : ⟨ ∅ ∈ˢ lam ⟩, and the brief's
--                    telescope cannot supply it (closedω ∅ holds vacuously,
--                    ∅ ∉ ∅).  pr∈λ's own body never reads ∅∈λ, T-ord or
--                    T-trans, so those three legs are DROPPED and the body
--                    is transcribed at the concrete facts Lset-out′,
--                    Lset-mono, pr∈Lset-suc.  Lset-out′ is IMPORTED from
--                    src/L/Coding/Bound.lagda.md, not recopied.
--   FLOOR            This file first checks with {!floor!} holes standing
--                    in for the proof bodies, to price the elaboration
--                    frame; the holes are then filled (floor-first law).
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-748.Probe748 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Coding {ℓ} using ( pr )
open import V.Model {ℓ} using ( ∈sucV-elim )
open import L.Constructible {ℓ} using ( IsOrd; Lset; Lset-mono )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡ )
open import L.Ordinal.StageArith {ℓ} lem
  using ( +ω; +ω-mem; closedω )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Axioms.Basic {ℓ} using ( pr∈Lset-suc )
open import L.Coding.Bound {ℓ} lem using ( Lset-out′ )
import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma using ( _×_; _,_ )
import Cubical.Data.Empty as Empty
open import Cubical.Foundations.HLevels using ( isOfHLevelLift )
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

------------------------------------------------------------------------------
-- SECTION 1.  The successor leg at (γ oγ clγ).  Verbatim from
-- [LJ-1.737-SPLIT]'s Closer (Probe737Split.agda:106-127); the hγ argument
-- is dropped because no-succ and suc∈γ never read it.

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
-- SECTION 2.  The pairing closure at a limit, transcribed from
-- BoundOver.pr∈λ (src/L/Coding/Bound.lagda.md:67-91) at T := Lset.
-- Dropped legs:  ∅∈λ (unsuppliable at this telescope, unread by the body),
-- T-ord and T-trans (unread by the body).

module PairLim (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩) where

  At : V ℓ → Type (ℓ-suc ℓ)
  At x = Σ[ δ ∈ V ℓ ] (⟨ δ ∈ˢ lam ⟩ × ⟨ x ∈ˢ Lset (sucV δ) ⟩)

  pr∈λ : (x y : V ℓ) → ⟨ x ∈ˢ Lset lam ⟩ → ⟨ y ∈ˢ Lset lam ⟩
       → ⟨ pr x y ∈ˢ Lset lam ⟩
  pr∈λ x y hx hy = PT.rec (snd (pr x y ∈ˢ Lset lam))
    (λ px → PT.rec (snd (pr x y ∈ˢ Lset lam)) (both px) (Lset-out′ lam y hy))
    (Lset-out′ lam x hx)
    where
    climb : (σ : V ℓ) → ⟨ σ ∈ˢ lam ⟩ → ⟨ x ∈ˢ Lset σ ⟩ → ⟨ y ∈ˢ Lset σ ⟩
          → ⟨ pr x y ∈ˢ Lset lam ⟩
    climb σ σ∈ hxσ hyσ =
      Lset-mono {α = lam} {β = sucV (sucV σ)}
        (succλ (sucV σ) (succλ σ σ∈)) {x = pr x y}
        (pr∈Lset-suc σ x y hxσ hyσ)
    both : At x → At y → ⟨ pr x y ∈ˢ Lset lam ⟩
    both (δ , (δ∈ , hxδ)) (ε , (ε∈ , hyε)) =
      Sum.rec
        (λ p → climb (sucV ε) (succλ ε ε∈)
                 (Lset-mono {α = sucV ε} {β = sucV δ} p {x = x} hxδ) hyε)
        (Sum.rec
          (λ q → climb (sucV ε) (succλ ε ε∈)
                   (subst (λ w → ⟨ x ∈ˢ Lset w ⟩) q hxδ) hyε)
          (λ r → climb (sucV δ) (succλ δ δ∈) hxδ
                   (Lset-mono {α = sucV δ} {β = sucV ε} r {x = y} hyε)))
        (ord-tri (sucV δ) (suc-ord {A = δ} (mem-ord {A = lam} ordλ δ δ∈))
                 (sucV ε) (suc-ord {A = ε} (mem-ord {A = lam} ordλ ε ε∈)))

------------------------------------------------------------------------------
-- THE OBLIGATION.  pr∈λ at lam := γ with the closedω successor leg as
-- succλ, at the top-level name the brief and the meter read.

pr-in-Lset-lim :
    (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
    (x y : V ℓ)
    → ⟨ x ∈ˢ Lset γ ⟩ → ⟨ y ∈ˢ Lset γ ⟩
    → ⟨ pr x y ∈ˢ Lset γ ⟩
pr-in-Lset-lim γ oγ clγ = PairLim.pr∈λ γ oγ (Closer.suc∈γ γ oγ clγ)
