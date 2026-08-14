{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.230] probe A.  THE STAGE-CARRIER DECODE.
--
-- [LJ-1.228] named the one probe that turns its band into a price:
-- write the two-way decode of the bounded level-hood graphBndAt at the
-- STAGE carrier (Lset lam), with the bound and the internal hierarchy
-- placed in Lset lam.  [LJ-1.123] named the class-carrier version and
-- nobody ran it.
--
-- This probe measures the object sl and sc SHARE (the stage-carrier
-- level-hood instantiation), not sl and sc themselves.
--
--   SECTION 1  the stage closure facts            (the placement)
--   SECTION 2  the stage-carrier decode           (the two directions)
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".  Tracked, never
-- deleted, and it lives beside its report.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-230.ProbeLJ1230A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
import FOL.Semantics
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _≐_; _∧̇_; ⊤̇; ∃̇_; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∃∈; δ-∀∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; Lset; Lset-in; Lset-out; Lset-mono; IsOrd; isTransV
        ; 𝒟ₒ; 𝒟ₒ-intro; Lset→isL )
open import L.Axioms.Basic {ℓ} using ( isL-Lset; Lset-suc )
open import L.Hull {ℓ} lem using ( module AtStage )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset→∈ )
open import L.Hierarchy {ℓ} lem using ( Lset-only; Lset-defines; hierL; hierL-spec )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Sigma using ( _×_; _,_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module CS = hPropStructure 𝒮ʟ

-- =====================================================================
-- SECTION 1: THE STAGE CLOSURE FACTS.
--
-- The stage carrier is Lset lam, an opaque atom to the elaborator.  A
-- level Lset b lands in the stage exactly when its ordinal b lands in
-- lam: Lset b ∈ Lset (sucV b) by definability, and sucV b ∈ lam by the
-- limit hypothesis succλ, so Lset-mono closes it.
-- =====================================================================

module StageDecode (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩) where

  module ASt = AtStage lam ordλ

  SL : Type (ℓ-suc ℓ)
  SL = ASt.SL

  -- The level at an ordinal below lam is a member of the stage.
  Lset∈Lset : (b : S) → IsOrd b → ⟨ b ∈ˢ lam ⟩ → ⟨ Lset b ∈ˢ Lset lam ⟩
  Lset∈Lset b ob b∈lam =
    Lset-mono {α = lam} {β = sucV b} (succλ b b∈lam)
      (subst (λ w → ⟨ Lset b ∈ˢ w ⟩) (sym (Lset-suc b))
        (𝒟ₒ-intro (Lset b) (Lset b) ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset b) ∣₁))

  -- The level as a stage member.
  Lv : (b : S) → IsOrd b → ⟨ b ∈ˢ lam ⟩ → SL
  Lv b ob b∈lam = Lset b , Lset∈Lset b ob b∈lam

  -- An ordinal of the stage is a member of lam.
  stageOrd∈lam : (b : SL) → IsOrd (fst b) → ⟨ fst b ∈ˢ lam ⟩
  stageOrd∈lam b ob = ord∈Lset→∈ lam ordλ (fst b) ob (snd b)

  -- ===================================================================
  -- SECTION 2: THE DECODE.  The class-carrier decode (Lset-only /
  -- Lset-defines) decodes LsetGraphAt, the UNBOUNDED graph, at the
  -- CLASS carrier CS.S (constructible sets).  The level-hood formula
  -- LevelHood0.Σ₂ consumes graphBndAt, the BOUNDED graph (leaf
  -- DefBodyB).  Moving the decode to the stage needs three bridges,
  -- and this section measures which close with the three named facts
  -- (isL-Lset, Lset-suc, succλ).
  -- ===================================================================

  -- The natural inclusion of the stage into the class carrier.
  -- DELIVERED (Lset→isL, src/L/Constructible.lagda.md:395).
  inCL : SL → CS.S
  inCL (x , x∈) = x , Lset→isL lam ordλ x x∈

  -- The level lands in the stage, and that is ALL the three named
  -- facts close (SECTION 1).  The write direction of the decode needs
  -- the BOUND and the internal HIERARCHY placed in Lset lam:
  --
  --   (a) a bound K with K ∈ Lset lam and hierL b ∈ K;
  --   (b) a bridge from the class carrier's inner semantics (⊨ over
  --       CS.S) to the stage carrier's (ASt.AbsL.⊨ᵐ over SL), for the
  --       constant-free level-hood formula;
  --   (c) the bounded graphBndAt ↔ unbounded LsetGraphAt agreement.
  --
  -- (c) is DELIVERED-AS-MACHINERY (LeafAgree / SatGraphAgree / KFacts,
  -- src/L/Condensation.lagda.md:6802-7230) but NOT assembled into a
  -- graphBndAt ↔ LsetGraphAt lemma (grep: none).  (b) is the carrier
  -- wall: mapFo needs a TOTAL map CS.S → SL, and there is none, since
  -- a constructible set need not lie in Lset lam.  (a) is the
  -- hierarchy wall: hierL b is built by hasReplacementL
  -- (src/L/Hierarchy.lagda.md:594-595), and no master states where
  -- the replacement image lands in the tower.
  --
  -- So the placement does NOT close with isL-Lset + Lset-suc + succλ.
  -- The three facts close the LEVEL placement only (SECTION 1).
