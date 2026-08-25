{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.541]  W3: THE ENVIRONMENT MATCH, ALONE.
--
-- The brief names the widest unmeasured term:
--
--   -- approx-carve's f, in the environment rankFo builds, at the pair
--
-- and orders it written FIRST, with the obligation omitted, and
-- typechecked ALONE.  This file is that.  `domAt` is not named here,
-- `domAt-intro` is not applied, the bound half is not built, and nothing
-- of `[LJ-1.529]` is imported.
--
-- WHAT IS MEASURED.  `[LJ-1.537]` reports that `approx-carve`'s
-- environment "is already the one `rankFo` builds" and checks it in a
-- SIDE file (agents/tasks/LJ-1-537/runs/Pin.agda:46-62), which pins the
-- three conjuncts at a hand-written environment.  It does NOT run them
-- inside `rankFo`.  So the term below places the carve where the formula
-- puts it: four existentials deep, under `rankFo`'s own binders, at the
-- pair `prʟ x (rank-at′ a oa x xa)`.  If the two environments differ,
-- this file is where the difference shows and the adapter would have to
-- be written.
--
-- IT IS THE WHOLE SATISFACTION HALF and nothing more.  Probe541.agda
-- section 3 carries the same term; a file cannot import the slice it was
-- cut from.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-541.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( var; con; _≐_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst; prAtL; prAtL-adequate )
open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
import Cubical.HITs.PropositionalTruncation as PT

import LJ-1-521.Probe521 {ℓ} lem as P521
import LJ-1-537.Probe537 {ℓ} lem as P537

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

private
  s2 : ∀ {n} → Fin n → Fin (suc (suc n))
  s2 i = suc (suc i)
  s3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  s3 i = suc (suc (suc i))

-- =====================================================================
--  THE FOUR EXISTENTIALS AND THE THREE CONJUNCTS.
--
--  `rankFo Q a` (Probe521.agda:493-501) at `(z ∷ [])` is
--
--    ∃ q. q ≐ Q ∧ ∃ m. ∃ r. ( prAtL z m r ∧ m ∈ a ∧ ∃ f. (fn ∧ asg ∧ sup) )
--
--  and the environment at the innermost point is `(f ∷ r ∷ m ∷ q ∷ z ∷ [])`,
--  which is `[LJ-1.521]`'s `Env.γ5` (Probe521.agda:512-516).  Every slot
--  below is filled by a DELIVERED term and by nothing else.
-- =====================================================================

module At (a : S) (oa : IsOrd (fst a)) (x : S) (xa : ⟨ fst x ∈ fst a ⟩) where

  -- slot q: `[LJ-1.521]`'s own witness, INSTANTIATED and not hypothesised
  -- (Probe521.agda:1162-1164).  This is `[LJ-1.537]`'s `Qwit`
  -- (Probe537.agda:581-582) and the same term.
  Q : S
  Q = P521.ord-set-witness a oa .fst

  -- slot r: the rank at the member (Probe521.agda:428-436).
  r : S
  r = P521.rank-at′ a oa x xa

  -- slot z: the pair the converse must exhibit.  This is `[LJ-1.537]`'s
  -- `Zof` (Probe537.agda:584-585) and the same term.
  z : S
  z = prʟ x r

  -- the first conjunct, at `q := Q`: `refl`.  `≈ˢ` on the model is
  -- `λ u v → fst u ≈ˢ fst v` (src/FOL/ZFStructure.lagda.md:148) over
  -- `𝒮ᵥ`'s path equality (src/V/Hierarchy.lagda.md:82).
  qQ : ⟨ (Q ∷ z ∷ []) ⊨ (var zero ≐ con Q) ⟩
  qQ = refl

  -- the second conjunct: the pair splits.  `prʟ-fst`
  -- (src/L/Coding/Model.lagda.md:329-330) enters through
  -- `prAtL-adequate` (:125-128).
  hpr : ⟨ (r ∷ x ∷ Q ∷ z ∷ []) ⊨ prAtL (s3 zero) (suc zero) zero ⟩
  hpr = subst ⟨_⟩
          (sym (prAtL-adequate (s3 zero) (suc zero) zero (r ∷ x ∷ Q ∷ z ∷ [])))
          (prʟ-fst x r)

  -- the third conjunct is `xa` itself, and the fourth existential is
  -- `[LJ-1.537]`'s carve WHOLE: `approx-carve a oa x xa` is a
  -- `Σ[ f ∈ S ] Approximates a oa x xa f` (Probe537.agda:616-620), and
  -- `Approximates` (:587-592) is the three conjuncts at `Env.γ5`.  It is
  -- passed as ONE term, so nothing here can re-spell the environment.
  sat : ⟨ (z ∷ []) ⊨ P521.rankFo Q a ⟩
  sat = PT.∣ Q , (qQ ,
          PT.∣ x ,
            PT.∣ r , (hpr , (xa , PT.∣ P537.approx-carve a oa x xa ∣₁)) ∣₁
          ∣₁) ∣₁

-- The environment match, as one top-level name.
carve-at-pair :
    (a : S) (oa : IsOrd (fst a)) (x : S) (xa : ⟨ fst x ∈ fst a ⟩)
  → ⟨ (prʟ x (P521.rank-at′ a oa x xa) ∷ [])
      ⊨ P521.rankFo (P521.ord-set-witness a oa .fst) a ⟩
carve-at-pair = At.sat
