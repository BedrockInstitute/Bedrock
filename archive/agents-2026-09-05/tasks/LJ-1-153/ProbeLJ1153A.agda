{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.153] probe A: the flagged SHAPES, turned from suspicion into fact.
--
-- `scripts/check-unbound-hyp.py` flags 38 telescope hypotheses.  A flag is
-- a suspicion.  This probe converts each SHAPE into a refutation, so that
-- the repair is priced against a fact.
--
-- FIVE SHAPES, one module each.  Every module ends in `Empty.⊥`, so the
-- hypothesis it names is an EMPTY TYPE and every theorem conditional on
-- it proves nothing.
--
--   Refute-val      rule 1, `valK`      (src/L/Condensation.lagda.md:3249)
--   Refute-val-un   rule 1, `valK-un`   (src/L/Condensation.lagda.md:2740)
--   Refute-codes    rule 2, `codesK`    (src/L/Condensation.lagda.md:6436)
--   Refute-entry    rule 2, `entryK`    (src/L/Condensation.lagda.md:6443)
--   Refute-dom      rule 2, `domK`      (src/L/Condensation.lagda.md:6713)
--
-- The two rule-1 shapes name the clause set through a SLOT, which a
-- refuter cannot choose, so they carry one hypothesis: the clause set
-- holds one code of the row's own shape.  The three rule-2 shapes
-- quantify over the containing set itself, so the refuter chooses it and
-- they carry NO hypothesis at all.
--
-- Nothing below uses any property of `K` beyond `K : S`.

open import Base.Prelude
open import Base.Truth

module LJ-1-153.ProbeLJ1153A {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Coding {ℓ} using ( pr )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst )
open import L.Axioms.Numerals {ℓ} using ( sucʟ; sucʟ-fst; numeralL; numeralL-fst )

open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_ )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

-- ===================================================================
-- THE ONE CONSTRUCTION THE THREE UNCONDITIONAL REFUTATIONS SHARE.
-- `sucʟ x` holds `x`, so it is the cheapest containing set there is,
-- and it exists at EVERY `x : S` with no side condition.
-- ===================================================================

self∈ : (x : S) → ⟨ fst x ∈ fst (sucʟ x) ⟩
self∈ x = subst (λ v → ⟨ fst x ∈ v ⟩) (sym (sucʟ-fst x)) (self∈sucV (fst x))

-- A code of the binary shape, built at chosen components.
binCode : ℕ → S → S → S → S
binCode k ar a b = prʟ ar (prʟ (numeralL k) (prʟ a b))

binShape : (k : ℕ) (ar a b : S)
         → fst (binCode k ar a b) ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
binShape k ar a b =
  prʟ-fst ar (prʟ (numeralL k) (prʟ a b))
  ∙ cong (pr (fst ar))
      (prʟ-fst (numeralL k) (prʟ a b)
       ∙ cong₂ pr (numeralL-fst k) (prʟ-fst a b))

-- A code of the unary shape.
unCode : ℕ → S → S → S
unCode k ar a = prʟ ar (prʟ (numeralL k) a)

unShape : (k : ℕ) (ar a : S)
        → fst (unCode k ar a) ≡ pr (fst ar) (pr (# k) (fst a))
unShape k ar a =
  prʟ-fst ar (prʟ (numeralL k) a)
  ∙ cong (pr (fst ar)) (prʟ-fst (numeralL k) a ∙ cong₂ pr (numeralL-fst k) refl)

-- ===================================================================
-- SHAPE 1.  `valK`, rule 1.  `yc` occurs in no premise, so instantiate
-- it at the bound `K` itself and regularity closes it.
-- The hypothesis is the row's own situation: its clause set holds one
-- code of its tag.
-- ===================================================================

module Refute-val (Cs K : S) (k : ℕ) (ar a b : S)
  (c∈ : ⟨ fst (binCode k ar a b) ∈ fst Cs ⟩) where

  absurd : ((k : ℕ) (c ar a b yc : S)
           → ⟨ fst c ∈ fst Cs ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
           → ⟨ fst yc ∈ fst K ⟩)
         → Empty.⊥
  absurd valK =
    ∈-irrefl (fst K) (valK k (binCode k ar a b) ar a b K c∈ (binShape k ar a b))

-- ===================================================================
-- SHAPE 2.  `valK-un`, rule 1.  The same defect at the five unary rows.
-- ===================================================================

module Refute-val-un (Cs K : S) (k : ℕ) (ar a : S)
  (c∈ : ⟨ fst (unCode k ar a) ∈ fst Cs ⟩) where

  absurd : ((k : ℕ) (c ar a yc : S)
           → ⟨ fst c ∈ fst Cs ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (fst a))
           → ⟨ fst yc ∈ fst K ⟩)
         → Empty.⊥
  absurd valK-un =
    ∈-irrefl (fst K) (valK-un k (unCode k ar a) ar a K c∈ (unShape k ar a))

-- ===================================================================
-- SHAPE 3.  `codesK`, rule 2.  The containing set `w` is the
-- hypothesis's OWN bound variable, so the refuter picks it.  Pick the
-- successor of a code whose every component is the bound `K`.
-- NO HYPOTHESIS.
-- ===================================================================

module Refute-codes (K : S) where

  absurd : ((w : S) (k : ℕ) (c ar a b : S)
           → ⟨ fst c ∈ fst w ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst K ⟩ × ⟨ fst a ∈ fst K ⟩ × ⟨ fst b ∈ fst K ⟩)
         → Empty.⊥
  absurd codesK =
    ∈-irrefl (fst K)
      (codesK (sucʟ (binCode 0 K K K)) 0 (binCode 0 K K K) K K K
        (self∈ (binCode 0 K K K)) (binShape 0 K K K) .fst)

-- ===================================================================
-- SHAPE 4.  `entryK`, rule 2.  The pair membership is satisfiable at a
-- set the author never intended.  NO HYPOTHESIS.
-- ===================================================================

module Refute-entry (K : S) where

  pairIn : ⟨ pr (fst K) (fst K) ∈ fst (sucʟ (prʟ K K)) ⟩
  pairIn = subst (λ v → ⟨ v ∈ fst (sucʟ (prʟ K K)) ⟩)
             (prʟ-fst K K) (self∈ (prʟ K K))

  absurd : ((w x y : S)
           → ⟨ pr (fst x) (fst y) ∈ fst w ⟩
           → ⟨ fst x ∈ fst K ⟩ × ⟨ fst y ∈ fst K ⟩)
         → Empty.⊥
  absurd entryK = ∈-irrefl (fst K) (entryK (sucʟ (prʟ K K)) K K pairIn .fst)

-- ===================================================================
-- SHAPE 5.  `domK`, rule 2.  The weakest of the three: it needs only
-- one set that holds `K`.  NO HYPOTHESIS.
-- ===================================================================

module Refute-dom (K : S) where

  absurd : ((d x : S) → ⟨ fst x ∈ fst d ⟩ → ⟨ fst x ∈ fst K ⟩) → Empty.⊥
  absurd domK = ∈-irrefl (fst K) (domK (sucʟ K) K (self∈ K))
