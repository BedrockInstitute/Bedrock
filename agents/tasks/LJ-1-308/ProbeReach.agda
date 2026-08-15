{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.308] REACH PROBE, the adversarial DD25 review of [LJ-1.306].
--
-- [LJ-1.306]'s `ProbeCompat.agda` checked the FIRST field of each of the
-- twelve row modules.  The external consumers write the LAST field, the
-- `*BndAt` one.  Ten of the twelve therefore went unchecked.  The same
-- probe checked `EnvSet.φB` and `EnvSet.φ`; `L.Coding.EnvSupply:444`
-- writes `EnvSet.back`.  And it checked two of the twelve clause names
-- that `LowerAgree.sixAt` and `UpperAgree.sixAt` write.
--
-- This probe checks what the consumers ACTUALLY reach:
--   A. all twelve clause names, generic-at-class against committed;
--   B. all twelve `*BndAt` row fields, original against generic;
--   C. `envSetAt`, generic-at-class against committed;
--   D. `EnvSet.back` in the consumer's own serving shape.
--
-- Consumer sites:
--   src/L/Condensation/LowerAgree.lagda.md:295-314 and :319-327
--   src/L/Condensation/UpperAgree.lagda.md:296-318 and :322-330
--   src/L/Coding/EnvSupply.lagda.md:440-444
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".  Lands nothing.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-308.ProbeReach {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ}
  using ( numeralL; numeralL-fst; pairʟ; pairʟ-fst; sucʟ; sucʟ-fst )
open import L.Coding.Model {ℓ}
  using ( envOverAt; envSetAt
        ; memClauseAt; eqClauseAt; andClauseAt; orClauseAt
        ; impClauseAt; negClauseAt
        ; topClauseAt; botClauseAt; existClauseAt; forallClauseAt
        ; allInClauseAt; exInClauseAt )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

import L.Condensation
import LJ-1-210.GenModel
import LJ-1-306.GenAgree

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

module Orig = L.Condensation {ℓ} lem
module Fam = LJ-1-306.GenAgree {ℓ} isL isL-trans
               numeralL numeralL-fst pairʟ pairʟ-fst sucʟ sucʟ-fst
module GMc = LJ-1-210.GenModel {ℓ} isL isL-trans
               numeralL numeralL-fst pairʟ pairʟ-fst sucʟ sucʟ-fst

-- =====================================================================
-- A.  THE TWELVE CLAUSE NAMES.  `LowerAgree.sixAt` and
-- `UpperAgree.sixAt` write the COMMITTED names; the ported `*Agree`
-- modules produce the GENERIC ones.  This is the load-bearing
-- cross-boundary identity, and [LJ-1.306] checked two of the twelve.
-- Arities follow the consumer sites exactly.
-- =====================================================================

chk-memClauseAt : ∀ {n : ℕ} (C T B : Fin n)
                → GMc.memClauseAt C T B ≡ memClauseAt C T B
chk-memClauseAt C T B = refl

chk-eqClauseAt : ∀ {n : ℕ} (C T B : Fin n)
               → GMc.eqClauseAt C T B ≡ eqClauseAt C T B
chk-eqClauseAt C T B = refl

chk-andClauseAt : ∀ {n : ℕ} (C T : Fin n)
                → GMc.andClauseAt C T ≡ andClauseAt C T
chk-andClauseAt C T = refl

chk-orClauseAt : ∀ {n : ℕ} (C T : Fin n)
               → GMc.orClauseAt C T ≡ orClauseAt C T
chk-orClauseAt C T = refl

chk-impClauseAt : ∀ {n : ℕ} (C T B : Fin n)
                → GMc.impClauseAt C T B ≡ impClauseAt C T B
chk-impClauseAt C T B = refl

chk-negClauseAt : ∀ {n : ℕ} (C T B : Fin n)
                → GMc.negClauseAt C T B ≡ negClauseAt C T B
chk-negClauseAt C T B = refl

chk-topClauseAt : ∀ {n : ℕ} (C T B : Fin n)
                → GMc.topClauseAt C T B ≡ topClauseAt C T B
chk-topClauseAt C T B = refl

chk-botClauseAt : ∀ {n : ℕ} (C T : Fin n)
                → GMc.botClauseAt C T ≡ botClauseAt C T
chk-botClauseAt C T = refl

chk-existClauseAt : ∀ {n : ℕ} (C T B : Fin n)
                  → GMc.existClauseAt C T B ≡ existClauseAt C T B
chk-existClauseAt C T B = refl

chk-forallClauseAt : ∀ {n : ℕ} (C T B : Fin n)
                   → GMc.forallClauseAt C T B ≡ forallClauseAt C T B
chk-forallClauseAt C T B = refl

chk-allInClauseAt : ∀ {n : ℕ} (C T B : Fin n)
                  → GMc.allInClauseAt C T B ≡ allInClauseAt C T B
chk-allInClauseAt C T B = refl

chk-exInClauseAt : ∀ {n : ℕ} (C T B : Fin n)
                 → GMc.exInClauseAt C T B ≡ exInClauseAt C T B
chk-exInClauseAt C T B = refl

-- =====================================================================
-- B.  THE TWELVE `*BndAt` ROW FIELDS.  These are the fields the two
-- `sixB` formulas name.  [LJ-1.306] checked `botBndAt` and `topBndAt`
-- only, because those are the first field of their module.
-- =====================================================================

chk-memBndAt : ∀ {m : ℕ} (C T B N K t0 t1 : Fin m)
             → Orig.Mem.memBndAt C T B N K t0 t1
             ≡ Fam.Mem.memBndAt C T B N K t0 t1
chk-memBndAt C T B N K t0 t1 = refl

chk-eqBndAt : ∀ {m : ℕ} (C T B N K t0 t1 : Fin m)
            → Orig.Eq.eqBndAt C T B N K t0 t1
            ≡ Fam.Eq.eqBndAt C T B N K t0 t1
chk-eqBndAt C T B N K t0 t1 = refl

chk-andBndAt : ∀ {m : ℕ} (C T B N K : Fin m)
             → Orig.And.andBndAt C T B N K ≡ Fam.And.andBndAt C T B N K
chk-andBndAt C T B N K = refl

chk-orBndAt : ∀ {m : ℕ} (C T B N K : Fin m)
            → Orig.Or.orBndAt C T B N K ≡ Fam.Or.orBndAt C T B N K
chk-orBndAt C T B N K = refl

chk-impBndAt : ∀ {m : ℕ} (C T B N K : Fin m)
             → Orig.Imp.impBndAt C T B N K ≡ Fam.Imp.impBndAt C T B N K
chk-impBndAt C T B N K = refl

chk-negBndAt : ∀ {m : ℕ} (C T B N K : Fin m)
             → Orig.Neg.negBndAt C T B N K ≡ Fam.Neg.negBndAt C T B N K
chk-negBndAt C T B N K = refl

chk-topBndAt : ∀ {m : ℕ} (C T B N K : Fin m)
             → Orig.Top.topBndAt C T B N K ≡ Fam.Top.topBndAt C T B N K
chk-topBndAt C T B N K = refl

chk-botBndAt : ∀ {m : ℕ} (C T B N K : Fin m)
             → Orig.Bot.botBndAt C T B N K ≡ Fam.Bot.botBndAt C T B N K
chk-botBndAt C T B N K = refl

chk-existBndAt : ∀ {m : ℕ} (C T B N K : Fin m)
               → Orig.Exist.existBndAt C T B N K
               ≡ Fam.Exist.existBndAt C T B N K
chk-existBndAt C T B N K = refl

chk-forallBndAt : ∀ {m : ℕ} (C T B N K : Fin m)
                → Orig.Forall.forallBndAt C T B N K
                ≡ Fam.Forall.forallBndAt C T B N K
chk-forallBndAt C T B N K = refl

chk-allInBndAt : ∀ {m : ℕ} (C T B N K t0 t1 : Fin m)
               → Orig.AllIn.allInBndAt C T B N K t0 t1
               ≡ Fam.AllIn.allInBndAt C T B N K t0 t1
chk-allInBndAt C T B N K t0 t1 = refl

chk-exInBndAt : ∀ {m : ℕ} (C T B N K t0 t1 : Fin m)
              → Orig.ExIn.exInBndAt C T B N K t0 t1
              ≡ Fam.ExIn.exInBndAt C T B N K t0 t1
chk-exInBndAt C T B N K t0 t1 = refl

-- =====================================================================
-- C.  `envSetAt`, the name `EnvSet.back`'s SOURCE type carries.
-- `L.Coding.EnvSupply:444` feeds it a term built at the committed name.
-- =====================================================================

chk-envSetAt : ∀ {n : ℕ} (E ar B : Fin n)
             → GMc.envSetAt E ar B ≡ envSetAt E ar B
chk-envSetAt E ar B = refl

-- =====================================================================
-- D.  `EnvSet.back` IN THE CONSUMER'S SHAPE.  The statement uses the
-- COMMITTED `envSetAt` and the ORIGINAL `envSetB`.  The term comes from
-- the GENERIC module.  This is `EnvSupply:444` exactly.
-- =====================================================================

served-EnvSet-back : ∀ {n : ℕ} (E ar B K : Fin n) (γ : S ^ n)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
          → ⟨ fst N ∈ fst (lookup K γ) ⟩ → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (E∈K : ⟨ fst (lookup E γ) ∈ fst (lookup K γ) ⟩)
  (ar∈K : ⟨ fst (lookup ar γ) ∈ fst (lookup K γ) ⟩)
  (envInK : (z : S) → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc ar) (suc B) ⟩
          → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  (h : ⟨ γ ⊨ envSetAt E ar B ⟩)
  → ⟨ γ ⊨ Orig.envSetB E ar B K ⟩
served-EnvSet-back E ar B K γ arityK E∈K ar∈K envInK h =
  Fam.EnvSet.back E ar B K γ arityK E∈K ar∈K envInK h
