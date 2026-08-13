{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.109] probe A: the key-fact family tied at the rows.
--
-- The five refuted facts (TwelveAgree.lagda.md:201-235) were consumed
-- in the master at the rows' sites.  [LJ-1.99] measured that every
-- site binds ar ∈ K and some also a ∈ K or b ∈ K; the tied shapes are
-- conditional on those memberships.  This dispatch states the five in
-- TIED form in the row telescopes and applies them at the site
-- binders.  This probe:
--
--   1. ATTEMPTS TO REFUTE the tied forms at the abstract frame.  Their
--      only candidate premise at the K-slot element is X ∈ X, refuted
--      by ∈-irrefl, so no tied form is forceable into a contradiction
--      (MEASURED unforceable, INFERRED not refuted).
--   2. MEASURES THE SUPPLY: the three tied shapes are DERIVABLE from
--      two closure primitives, sucK (the successor closure, which this
--      dispatch names but does NOT put into the KFacts record: a record
--      field with `sucV (fst a)` in its type WALLS the master, MEASURED
--      three times, P-i class 3) and pairK (the delivered KFacts
--      field).  The derivations are the terms the frame repair will
--      use to inhabit the tied facts.
--   3. ANCHORS THE SITE SUPPLY: the tied facts at the ForallAgree
--      layout applied at the row's binders give exactly the
--      memberships the transfers consume (SuccKeySite of [LJ-1.99],
--      GREEN).
--   4. CONSUMES the transfer signatures at an abstract frame (they are
--      UNCHANGED by this dispatch): SubValB2T and SubValSuccB2T close
--      out/back from their membership parameters.
--
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ1109A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( sucʟ; sucʟ-fst )
open import L.Coding.Model {ℓ}
  using ( prʟ; prʟ-fst; subValAt; subValSuccAt )
open import L.Condensation {ℓ} lem
  using ( module SubValB2T; module SubValSuccB2T; subValB; subValSuccB; succU; keyU )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; squash₁; ∥_∥₁ )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- 1. THE REFUTATION ATTEMPTS ON THE TIED FORMS.  The tied succK is
-- (a : S) → a ∈ K → sucV a ∈ K; the tied keyK shapes add a ∈ K (or
-- b ∈ K).  At the abstract frame the only way to force a premise is at
-- the K-slot element X, whose premise is X ∈ X, refuted by ∈-irrefl.
-- No tied form is forceable into a contradiction (MEASURED
-- unforceable; the non-refutation itself is INFERRED, exactly as
-- [LJ-1.105] recorded for the entryK and arSubK ties).
-- =====================================================================
module RefuteAttempts {m : ℕ} (K : Fin m) (γ : S ^ m) where

  A : V ℓ
  A = fst (lookup K γ)

  sucK-premise-refuted : ⟨ fst (lookup K γ) ∈ fst (lookup K γ) ⟩ → Empty.⊥
  sucK-premise-refuted = ∈-irrefl A

  keyK-premise-refuted : ⟨ fst (lookup K γ) ∈ fst (lookup K γ) ⟩ → Empty.⊥
  keyK-premise-refuted = ∈-irrefl A

-- =====================================================================
-- 2. THE SUPPLY, MEASURED.  The three tied shapes are derivable from
-- the two closure primitives at the generic K γ frame:
--   succ-tied    = sucK ar arK;
--   key-neg-tied = pairK transported along prʟ-fst (the prʟ pair is
--                  propositionally the hierarchy pair);
--   key-un-tied  = pairK on the L-successor of ar, whose fst is the
--                  hierarchy successor (sucʟ-fst), transported.
-- These terms inhabit the row telescopes' tied facts; they are what
-- the frame repair must supply (C-38).
-- =====================================================================
module TiesSupplied {m : ℕ} (K : Fin m) (γ : S ^ m)
  (sucK : (a : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩
          → ⟨ sucV (fst a) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩
           → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩) where

  succ-tied : (ar : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
            → ⟨ sucV (fst ar) ∈ fst (lookup K γ) ⟩
  succ-tied ar arK = sucK ar arK

  key-neg-tied : (ar a : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
               → ⟨ fst a ∈ fst (lookup K γ) ⟩
               → ⟨ pr (fst ar) (fst a) ∈ fst (lookup K γ) ⟩
  key-neg-tied ar a arK aK =
    subst (λ w → ⟨ w ∈ fst (lookup K γ) ⟩) (prʟ-fst ar a)
      (pairK ar a arK aK)

  key-un-tied : (ar a : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
              → ⟨ fst a ∈ fst (lookup K γ) ⟩
              → ⟨ pr (sucV (fst ar)) (fst a) ∈ fst (lookup K γ) ⟩
  key-un-tied ar a arK aK =
    subst (λ w → ⟨ w ∈ fst (lookup K γ) ⟩)
      (prʟ-fst (sucʟ ar) a ∙ cong₂ pr (sucʟ-fst ar) refl)
      (pairK (sucʟ ar) a
        (transport (sym (cong (λ w → ⟨ w ∈ fst (lookup K γ) ⟩) (sucʟ-fst ar)))
          (sucK ar arK))
        aK)

-- =====================================================================
-- 3. THE SITE SUPPLY, ANCHORED.  The tied facts at the ForallAgree
-- layout applied at the row's binders give exactly the memberships
-- the transfer consumes (this is [LJ-1.99]'s SuccKeySite, re-run on
-- the master's tied telescopes).
-- =====================================================================
module SiteSupply {m : ℕ} (C T B N K : Fin m) (γ : S ^ m)
  (succK : (E ya yc a ar c : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
          → succU {m} C T B N K γ E ya yc a ar c)
  (keyK : (E ya yc a ar c : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
          → ⟨ fst a ∈ fst (lookup K γ) ⟩
          → keyU {m} C T B N K γ E ya yc a ar c)
  (E ya yc a ar c : S)
  (arK : ⟨ fst ar ∈ fst (lookup K γ) ⟩)
  (aK : ⟨ fst a ∈ fst (lookup K γ) ⟩) where

  succK-use : succU {m} C T B N K γ E ya yc a ar c
  succK-use = succK E ya yc a ar c arK

  keyK-use : keyU {m} C T B N K γ E ya yc a ar c
  keyK-use = keyK E ya yc a ar c arK aK

-- =====================================================================
-- 4. THE CONSUMER (C-35/C-38).  The transfer signatures are unchanged
-- by this dispatch: SubValB2T and SubValSuccB2T take the memberships
-- and close both directions at an abstract frame.
-- =====================================================================
module TransferUse {m : ℕ} (T ar a y K : Fin m) (γ : S ^ m)
  (succK : ⟨ sucV (fst (lookup ar γ)) ∈ fst (lookup K γ) ⟩)
  (keyK : ⟨ pr (sucV (fst (lookup ar γ))) (fst (lookup a γ)) ∈ fst (lookup K γ) ⟩) where

  module S = SubValSuccB2T {m} T ar a y K γ succK keyK

  out-s : ⟨ γ ⊨ subValSuccAt T ar a y ⟩
        → ∥ Σ S (λ z₁ → ⟨ fst z₁ ∈ fst (lookup K γ) ⟩
            × ⟨ (z₁ ∷ γ) ⊨ S.core₁ ⟩
            × ∥ Σ S (λ z₂ → ⟨ fst z₂ ∈ fst (lookup (suc K) (z₁ ∷ γ)) ⟩
                × ⟨ (z₂ ∷ z₁ ∷ γ) ⊨ S.core₂ ⟩) ∥₁) ∥₁
  out-s = S.out

  back-s : ⟨ γ ⊨ subValSuccB T ar a y K ⟩ → ⟨ γ ⊨ subValSuccAt T ar a y ⟩
  back-s = S.back

module TransferUseNeg {m : ℕ} (T ar a y K : Fin m) (γ : S ^ m)
  (keyK : ⟨ pr (fst (lookup ar γ)) (fst (lookup a γ)) ∈ fst (lookup K γ) ⟩) where

  module B = SubValB2T {m} T ar a y K γ keyK

  out-b : ⟨ γ ⊨ subValAt T ar a y ⟩
        → ∥ Σ S (λ z → ⟨ fst z ∈ fst (lookup K γ) ⟩ × ⟨ (z ∷ γ) ⊨ B.core ⟩) ∥₁
  out-b = B.out

  back-b : ⟨ γ ⊨ subValB T ar a y K ⟩ → ⟨ γ ⊨ subValAt T ar a y ⟩
  back-b = B.back
