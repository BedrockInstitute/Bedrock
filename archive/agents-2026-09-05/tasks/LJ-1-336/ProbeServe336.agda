{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.336] SERVING PROBE.  C-40, applied to wave 2.
--
-- `[LJ-1.308]` found wave 1's serving evidence tested names the consumers
-- do NOT write.  Wave 2 must not repeat that.  So this file starts from the
-- CONSUMERS, measured by grep over `src`:
--
--   src/L/BoundedSubset.lagda.md:30, :82, :90, :115, :124  reach `DefBodyB`
--     and `Δ₀-DefBodyB`;
--   src/L/Condensation/TwelveAgree.lagda.md:31, :529, :534  reach
--     `module SatGraphB`, and write `SatGraphB.twelveB`.
--
-- Those two blocks are in WAVE 2's copy set, not wave 1's.  The seven
-- `Agree` modules themselves have ZERO external reaches, MEASURED by the
-- same grep, so the family's own serving surface is internal.
--
-- Section A checks the eight re-stated gap names, generic-at-class against
-- the committed `L.Coding.*` deliveries.  Section B checks the two
-- externally consumed blocks.  Section C states one of the seven in the
-- consumer's own shape: the ORIGINAL names in the type, the GENERIC
-- module's field as the term.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-336.ProbeServe336 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ}
  using ( numeralL; numeralL-fst; pairʟ; pairʟ-fst; sucʟ; sucʟ-fst )
open import L.Coding.CodeSet {ℓ} lem using ( hasWitnessAt; keyArityAtL )
open import L.Coding.Graph {ℓ} lem using ( twelveAt )
open import L.Coding.Powerset {ℓ} lem using ( isCodeAt; DefinesAt; envOneAt )
open import L.Coding.Model {ℓ} using ( tagAtL )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

import L.Condensation
import LJ-1-336.GenDirty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

module Orig = L.Condensation {ℓ} lem
module Fam = LJ-1-336.GenDirty {ℓ} isL isL-trans
               numeralL numeralL-fst pairʟ pairʟ-fst sucʟ sucʟ-fst

-- =====================================================================
-- A.  THE RE-STATED GAP NAMES, generic-at-class against the committed
-- `L.Coding.*` deliveries.  `satGraphAt` and `DefBody` are NOT here, and
-- section D says why.
-- =====================================================================

chk-keyArityAtL : ∀ {n : ℕ} (c : Fin n) (k : ℕ)
                → Fam.keyArityAtL c k ≡ keyArityAtL c k
chk-keyArityAtL c k = refl

chk-hasWitnessAt : ∀ {n : ℕ} (A x : Fin n)
                 → Fam.hasWitnessAt A x ≡ hasWitnessAt A x
chk-hasWitnessAt A x = refl

chk-twelveAt : ∀ {n : ℕ} (C T B : Fin n)
             → Fam.twelveAt C T B ≡ twelveAt C T B
chk-twelveAt C T B = refl

chk-envOneAt : ∀ {n : ℕ} (e y : Fin n)
             → Fam.envOneAt e y ≡ envOneAt e y
chk-envOneAt e y = refl

chk-DefinesAt : ∀ {n : ℕ} (x w v : Fin n)
              → Fam.DefinesAt x w v ≡ DefinesAt x w v
chk-DefinesAt x w v = refl

chk-isCodeAt : ∀ {n : ℕ} (c w : Fin n)
             → Fam.isCodeAt c w ≡ isCodeAt c w
chk-isCodeAt c w = refl

-- =====================================================================
-- B.  THE TWO BLOCKS WITH EXTERNAL CONSUMERS, original against generic.
-- These are the names `L.BoundedSubset` and `L.Condensation.TwelveAgree`
-- actually write.
-- =====================================================================

chk-DefBodyB : ∀ {n : ℕ} (w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11
                          t0 t1 : Fin (5 + n))
             → Orig.DefBodyB {n} w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
             ≡ Fam.DefBodyB {n} w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
chk-DefBodyB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 = refl

chk-twelveB : ∀ {n : ℕ} (w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11
                         t0 t1 : Fin (5 + n))
            → Orig.SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
            ≡ Fam.SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
chk-twelveB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 = refl

chk-satGraphB : ∀ {n : ℕ} (w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11
                           t0 t1 : Fin (5 + n))
              → Orig.SatGraphB.satGraphB {n} w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
              ≡ Fam.SatGraphB.satGraphB {n} w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
chk-satGraphB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 = refl

-- The three bounded blocks the seven need that wave 1 did not port.
chk-keyArBS : ∀ {n : ℕ} (c tag K : Fin n)
            → Orig.keyArBS c tag K ≡ Fam.keyArBS c tag K
chk-keyArBS c tag K = refl

chk-envOneBndS : ∀ {n : ℕ} (v K N0 : Fin n)
               → Orig.envOneBndS v K N0 ≡ Fam.envOneBndS v K N0
chk-envOneBndS v K N0 = refl

chk-DefinesBS : ∀ {n : ℕ} (x w v K N0 : Fin n)
              → Orig.DefinesBS x w v K N0 ≡ Fam.DefinesBS x w v K N0
chk-DefinesBS x w v K N0 = refl

chk-isCodeBS : ∀ {n : ℕ} (c w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin n)
             → Orig.isCodeBS c w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11
             ≡ Fam.isCodeBS c w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11
chk-isCodeBS c w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 = refl

chk-hasWitnessBS : ∀ {n : ℕ} (A x K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin n)
                 → Orig.hasWitnessBS A x K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11
                 ≡ Fam.hasWitnessBS A x K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11
chk-hasWitnessBS A x K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 = refl

-- =====================================================================
-- C.  ONE OF THE SEVEN, IN A CONSUMER'S OWN SHAPE.  The type names the
-- ORIGINAL `envOneAt` and `envOneBndS`; the term is the GENERIC module's
-- field.  The ties stay hypotheses, because a serving check is about the
-- types, not about a site.
-- =====================================================================

module Serve {m : ℕ} (v K N0 : Fin m) (γ : S ^ (2 + m))
  (N0eq : fst (lookup (suc (suc N0)) γ) ≡ fst (numeralL 0))
  (numK : ⟨ fst (numeralL 0) ∈ fst (lookup (suc (suc K)) γ) ⟩)
  (pairK : (z : S) → ⟨ (z ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
          → ⟨ fst z ∈ fst (lookup (suc (suc K)) γ) ⟩) where

  -- ONE telescope, copied verbatim from src/L/Condensation.lagda.md:6748
  -- to :6752, serves BOTH module declarations.
  module O = Orig.EnvOneAgree v K N0 γ N0eq numK pairK
  module F = Fam.EnvOneAgree v K N0 γ N0eq numK pairK

  -- The type is the ORIGINAL's, at the committed `envOneAt` and the
  -- committed `envOneBndS`.  The term is the GENERIC module's field.
  served-out : ⟨ γ ⊨ envOneAt zero (suc zero) ⟩
             → ⟨ γ ⊨ Orig.envOneBndS v K N0 ⟩
  served-out = F.out

  served-back : ⟨ γ ⊨ Orig.envOneBndS v K N0 ⟩
              → ⟨ γ ⊨ envOneAt zero (suc zero) ⟩
  served-back = F.back
