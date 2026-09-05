{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.737] PROBE.  table-sat at the [LJ-1.698] Carved frame
-- (Probe698.agda:107-123), under closedω γ (StageArith.lagda.md:81-82).
-- Lands nothing in src/.
--
--   THE OBLIGATION   table-sat.  NOT INHABITED.  See the ABSENCE block
--                    at the file's end and lj-1.737-report.md.
--   DELIVERED        Closer: the closedω arithmetic the whole route
--                    stands on -- no-succ (closedω γ is never a
--                    successor), suc∈γ, iter∈γ, block∈Lγ (StageArith's
--                    boundCloses turned into a finite-iterate kit).
--                    pair-in-Lγω: pr x (Lset x) ∈ˢ Lset γ from x ∈ γ
--                    alone, where [LJ-1.724-SPLIT] needed x+2 < γ as a
--                    hypothesis.  This is the conclusion-side placement
--                    the 724-SPLIT scope could not give.
--   NOT DELIVERED    the A-restricted satisfaction of φᵣ.  Two debts
--                    block it, both measured, neither probe-sized:
--                    (i) the stage bound for mkBoundedFo ψᵣ, which
--                    needs a constant-tracking induction over the
--                    recording's atom unfolding (the tag atoms carry
--                    numeralL constants -- CodeSet.lagda.md:135-136);
--                    (ii) the DefAt-witness placement: nothing in
--                    src/ places keyS/Sat witnesses in a controlled
--                    stage (EnvSet's stageFor bounds are boundingOrd
--                    sups, EnvSet.lagda.md:85-99, uncontrolled).
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-737.Probe737 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Coding {ℓ} using ( pr )
open import V.Model {ℓ} using ( ∈sucV-elim )
open import L.Constructible {ℓ}
  using ( isL; IsOrd; Lset; Lset-mono )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Ordinal.Stages {ℓ} lem
  using ( suc∈or≡ )
open import L.Ordinal.StageArith {ℓ} lem
  using ( sucIter; +ω; +ω-iter; +ω-mem
        ; closedω; boundCloses )
open import LJ-1-724-SPLIT.Probe724Split {ℓ} lem
  using ( module Frame )
open import Cubical.Data.Sum as Sum using ( _⊎_ )
import Cubical.Data.Empty as Empty
open import Cubical.Foundations.HLevels using ( isOfHLevelLift )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

------------------------------------------------------------------------------
-- SECTION 1.  closedω arithmetic.  Every leg is one StageArith call
-- plus transitivity of the ordinal γ.

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

  iter∈γ : (n : ℕ) (x : V ℓ) → ⟨ x ∈ˢ γ ⟩ → ⟨ sucIter n x ∈ˢ γ ⟩
  iter∈γ zero x x∈ = x∈
  iter∈γ (suc n) x x∈ = suc∈γ (sucIter n x) (iter∈γ n x x∈)

  -- Any member of a finite iterate's stage lands in Lset γ.  This is
  -- StageArith's boundCloses with the iterate bound folded in.
  block∈Lγ : (n : ℕ) (x : V ℓ) → ⟨ x ∈ˢ γ ⟩
           → (b : V ℓ) → ⟨ b ∈ˢ Lset (sucIter n x) ⟩ → ⟨ b ∈ˢ Lset γ ⟩
  block∈Lγ n x x∈ b b∈ =
    boundCloses γ x clγ x∈ b
      (Lset-mono {α = +ω x} {β = sucIter n x} (+ω-iter n x) b∈)

------------------------------------------------------------------------------
-- SECTION 2.  The conclusion-side placement under closedω.  [LJ-1.724-
-- SPLIT] placed pr x (Lset x) in Lset γ only at the scope x+2 < γ;
-- closedω derives that iterate membership, so the placement holds for
-- EVERY member x.  Frame's pair-in-Lγ is reused as the breadth leg.

module Underω (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩) (clγ : closedω γ) where

  open Closer γ oγ hγ clγ

  x²∈γ : (x : V ℓ) → ⟨ x ∈ˢ γ ⟩ → ⟨ sucV (sucV x) ∈ˢ γ ⟩
  x²∈γ x x∈ = suc∈γ (sucV x) (suc∈γ x x∈)

  pair-in-Lγω : (x : V ℓ) → ⟨ x ∈ˢ γ ⟩ → ⟨ pr x (Lset x) ∈ˢ Lset γ ⟩
  pair-in-Lγω x x∈ =
    Frame.pair-in-Lγ γ oγ hγ x (mem-ord {A = γ} oγ x x∈) (x²∈γ x x∈)

------------------------------------------------------------------------------
-- THE OBLIGATION IS ABSENT ON PURPOSE.  No postulate stands in for it
-- and no weaker form is inhabited under its name.
--
--   table-sat : (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩)
--                 (clγ : closedω γ)
--                 (x : V ℓ) → ⟨ x ∈ˢ γ ⟩
--               → ⟨ ω ∈ˢ γ ⟩
--             → ⟨ pr x (Lset x) ∈ˢ Carved.carved γ oγ hγ ⟩
--
-- The target is TRUE (D-10 truth-price):  the satisfaction witnesses the
-- A-restricted reading demands -- the recording witness x, the value slot
-- Lset x, the tower graph below x, the step's c'/Lset c'/𝒟ₒ (Lset c')
-- with 𝒟ₒ (Lset c') = Lset (sucV c') by Lset-suc, and DefAt's code and
-- graph -- all have rank finite over members of γ, and closedω absorbs
-- each finite block (Section 1).  What blocks the GO is not the target
-- but two TREE debts, and neither is probe-sized:
--
--   (i)  The tower graph below x must be carved at a CONTROLLED stage.
--        mkBoundedFo ψᵣ hands a stage σₘ with no bound, and bounding it
--        needs a constant-tracking induction over the recording's atom
--        unfolding:  the tag atoms carry con (numeralL k) constants
--        (src/L/Coding/CodeSet.lagda.md:135-136, Model.lagda.md:585-587),
--        and no per-constant bound is uniform over that unfolding.
--   (ii) DefAt's witnesses (code and graph, keyS/Sat over the value)
--        have no placement leg anywhere:  EnvSet's stageFor bounds are
--        boundingOrd sups of least-stages (src/L/Coding/EnvSet.lagda.md
--        :85-99), not finite iterates, and StageArith's header comment
--        ("the code set over the carrier at δ sits at stage δ+ω",
--        StageArith.lagda.md:76-80) is narrative only -- boundCloses
--        waits for exactly the leg that would supply it.
--
-- The full route, with these two debts paid, is in lj-1.737-report.md.
