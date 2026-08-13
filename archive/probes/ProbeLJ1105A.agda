{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.105] probe A: the landed EnvSet and the Mem row.
--
-- The master now derives the two ties inside EnvSet: EnvSet carries
-- arityK, E ∈ K and ar ∈ K and derives the ChainZ entryK tie and
-- the arSubK tie once (src/L/Condensation.lagda.md, module ChainZ
-- before EnvSet).  The Mem row states only arityK; tmKeyK, entryK
-- and arSubK are gone from its telescope, and the key membership is
-- derived inside AtomLeaf from arityK plus the code slot's
-- membership.
--
-- This probe does four things:
--   1. REFUTES the tied keyValK form (regression guard for why
--      tmKeyK cannot be a telescope hypothesis), exactly as
--      [LJ-1.104] measured it.
--   2. MEASURES the supply of both ties: the master's ChainZ builds
--      entryK and arSubK from arityK alone.
--   3. Records the refutation ATTEMPTS on the two ties: their
--      premises (z ∈ K, ar ∈ K) are not forceable at the K-slot
--      element, which is X ∈ X refuted by ∈-irrefl.
--   4. CONSUMES the new EnvSet at an abstract frame (C-15): out,
--      back and memE-bnd all close with the three new parameters.
--
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ1105A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ}
  using ( envOverAt; envSetAt; tagAtL; tagAtL-adequate; prʟ; prʟ-fst )
open import L.Condensation {ℓ} lem
  using ( module ChainZ; module EnvSet; envSetB )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_ )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
open AbsL using ( _^_ )

-- =====================================================================
-- 1. THE keyValK REFUTATION, MEASURED (regression guard).  The tied
-- tmKeyK of [LJ-1.102] is an empty type at the abstract frame: the
-- code slot and the key are both quantified variables, so the tag
-- satisfaction can be forced at the K-slot element, and the
-- conclusion is X ∈ X.  This is why tmKeyK is derived, not stated.
-- =====================================================================
module RefuteKeyValK {m : ℕ} (K : Fin m) (γ : S ^ m) where

  X : S
  X = lookup K γ

  A : V ℓ
  A = fst X

  env : S ^ (11 + m)
  env = X ∷ X ∷ X ∷ X ∷ X ∷ X ∷ X ∷ prʟ (numeralL 1) X ∷ X ∷ X ∷ X ∷ γ

  tagEq : fst (lookup (suc (suc (suc (suc (suc (suc (suc zero))))))) env)
        ≡ pr (# 1) (fst (lookup zero env))
  tagEq = prʟ-fst (numeralL 1) X ∙ cong₂ pr (numeralL-fst 1) refl

  premise : ⟨ env ⊨ tagAtL (suc (suc (suc (suc (suc (suc (suc zero))))))) 1 zero ⟩
  premise = transport (cong fst (sym
              (tagAtL-adequate (suc (suc (suc (suc (suc (suc (suc zero)))))))
                                1 zero env))) tagEq

  keyValK-type : Type (ℓ-suc ℓ)
  keyValK-type = (E yc b a ar c w v z k : S)
               → ⟨ (k ∷ w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                    tagAtL (suc (suc (suc (suc (suc (suc (suc zero))))))) 1 zero ⟩
               → ⟨ fst k ∈ fst (lookup K γ) ⟩

  keyValK-refutes : keyValK-type → Empty.⊥
  keyValK-refutes keyValK = ∈-irrefl A
    (keyValK X X X (prʟ (numeralL 1) X) X X X X X X premise)

-- =====================================================================
-- 2. THE SUPPLY, MEASURED.  The master's ChainZ derives both ties
-- from arityK alone, and EnvSet derives them inside itself.  These
-- aliases pin the derived types.
-- =====================================================================
module TiesSupplied {m : ℕ} (K : Fin m) (γ : S ^ m)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
          → ⟨ fst N ∈ fst (lookup K γ) ⟩
          → ⟨ fst v ∈ fst (lookup K γ) ⟩) where

  module Z = ChainZ {m} K γ arityK

  entryK-supplied : (z x y : S) → ⟨ fst z ∈ fst (lookup K γ) ⟩
                  → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
                  → ⟨ fst x ∈ fst (lookup K γ) ⟩
                    × ⟨ fst y ∈ fst (lookup K γ) ⟩
  entryK-supplied = Z.entryK-tied-zK

  arSubK-supplied : (ar x : S) → ⟨ fst x ∈ fst ar ⟩
                  → ⟨ fst ar ∈ fst (lookup K γ) ⟩
                  → ⟨ fst x ∈ fst (lookup K γ) ⟩
  arSubK-supplied = Z.arSubK-tied

-- =====================================================================
-- 3. THE REFUTATION ATTEMPTS ON THE TIES.  The entryK tie's premise
-- z ∈ K is not forceable at the K-slot element (it would be X ∈ X,
-- refuted by ∈-irrefl), and the arSubK tie's ar ∈ K premise is the
-- same.  Neither tie is refutable at the abstract frame; both are
-- supplied by the measured derivations above.
-- =====================================================================
module RefuteAttempts {m : ℕ} (K : Fin m) (γ : S ^ m) where

  A : V ℓ
  A = fst (lookup K γ)

  zK-premise-refuted : ⟨ fst (lookup K γ) ∈ fst (lookup K γ) ⟩ → Empty.⊥
  zK-premise-refuted = ∈-irrefl A

  arK-premise-refuted : ⟨ fst (lookup K γ) ∈ fst (lookup K γ) ⟩ → Empty.⊥
  arK-premise-refuted = ∈-irrefl A

-- =====================================================================
-- 4. THE CONSUMER (C-15).  The new EnvSet closes both directions at
-- an abstract frame from arityK, E ∈ K and ar ∈ K plus envInK.
-- =====================================================================
module EnvSetUse {n : ℕ} (E ar B K : Fin n) (γ : S ^ n)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
          → ⟨ fst N ∈ fst (lookup K γ) ⟩
          → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (E∈K : ⟨ fst (lookup E γ) ∈ fst (lookup K γ) ⟩)
  (ar∈K : ⟨ fst (lookup ar γ) ∈ fst (lookup K γ) ⟩)
  (envInK : (z : S) → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc ar) (suc B) ⟩
          → ⟨ fst z ∈ fst (lookup K γ) ⟩) where

  module E' = EnvSet {n} E ar B K γ arityK E∈K ar∈K envInK

  out-use : ⟨ γ ⊨ envSetB E ar B K ⟩ → ⟨ γ ⊨ envSetAt E ar B ⟩
  out-use = E'.out

  back-use : ⟨ γ ⊨ envSetAt E ar B ⟩ → ⟨ γ ⊨ envSetB E ar B K ⟩
  back-use = E'.back

  memE-use : ⟨ γ ⊨ envSetB E ar B K ⟩
           → (z : S) → ⟨ fst z ∈ fst (lookup E γ) ⟩
           → ⟨ fst z ∈ fst (lookup K γ) ⟩
  memE-use = E'.memE-bnd
