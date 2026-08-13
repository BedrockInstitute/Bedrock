{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.99] probe B: the EnvSet site does not bind E ∈ K, and does
-- not bind ar ∈ K.  RED as designed.
--
-- The EnvSet module (src/L/Condensation.lagda.md:2771-2777) takes
-- entryK, arSubK and envInK as parameters, plus the slots E ar B K
-- and γ.  None of the three parameters concludes E ∈ K: entryK
-- concludes x ∈ K and y ∈ K from a pair membership in z; arSubK
-- concludes x ∈ K from x ∈ ar; envInK concludes z ∈ K from an
-- envOverAt satisfaction.  The site-use lemma from the four-step
-- chain (ProbeLJ199A.Chain.entryK-tied) therefore needs the E ∈ K
-- premise as a hole, and it stays unsolved: exit 42.  The same holds
-- for the arSubK tie: arityK once needs ar ∈ K, and the telescope
-- does not bind it.
--
-- The frame facts envK-* (TwelveAgree.lagda.md:98-117) conclude
-- E ∈ K from an envSetAt satisfaction; the rows bind that
-- satisfaction (hE) and derive EK, so the row level DOES supply the
-- premise (read from the source, section 2 of the report).  This
-- probe measures only the EnvSet telescope itself.
--
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ199B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ} using ( envOverAt )
open import ProbeLJ199A {ℓ} lem

open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
open AbsL using ( _^_ )

-- The EnvSet telescope, plus the one field the repair would add
-- (arityK).  The site-use lemma from the four-step chain cannot be
-- written: the chain's step 1 needs E ∈ K, and the telescope has no
-- binder for it.  The hole below is exactly that membership, and it
-- stays unsolved.
module EnvSetSiteNoEK {n : ℕ} (E ar B K : Fin n) (γ : S ^ n)
  (entryK : (z x y : S) → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
          → ⟨ fst x ∈ fst (lookup K γ) ⟩
            × ⟨ fst y ∈ fst (lookup K γ) ⟩)
  (arSubK : (x : S) → ⟨ fst x ∈ fst (lookup ar γ) ⟩
           → ⟨ fst x ∈ fst (lookup K γ) ⟩)
  (envInK : (z : S) → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc ar) (suc B) ⟩
           → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
          → ⟨ fst N ∈ fst (lookup K γ) ⟩
          → ⟨ fst v ∈ fst (lookup K γ) ⟩) where

  -- This term cannot be written: the E ∈ K premise is absent from
  -- the site's binders.  Red, as designed.
  envEntry-use : (z x y : S) → ⟨ fst z ∈ fst (lookup E γ) ⟩
               → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
               → ⟨ fst x ∈ fst (lookup K γ) ⟩
                 × ⟨ fst y ∈ fst (lookup K γ) ⟩
  envEntry-use z x y z∈E p = Chain.entryK-tied {n} E K γ arityK ? z x y z∈E p

-- The arSubK use at the same site: arityK once needs ar ∈ K, and
-- the telescope does not bind it.  The hole below is that membership.
module EnvSetSiteNoArK {n : ℕ} (E ar B K : Fin n) (γ : S ^ n)
  (entryK : (z x y : S) → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
          → ⟨ fst x ∈ fst (lookup K γ) ⟩
            × ⟨ fst y ∈ fst (lookup K γ) ⟩)
  (arSubK : (x : S) → ⟨ fst x ∈ fst (lookup ar γ) ⟩
           → ⟨ fst x ∈ fst (lookup K γ) ⟩)
  (envInK : (z : S) → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc ar) (suc B) ⟩
           → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
          → ⟨ fst N ∈ fst (lookup K γ) ⟩
          → ⟨ fst v ∈ fst (lookup K γ) ⟩) where

  -- This term cannot be written: the ar ∈ K premise is absent from
  -- the site's binders.  Red, as designed.
  arSubK-use : (x : S) → ⟨ fst x ∈ fst (lookup ar γ) ⟩
             → ⟨ fst x ∈ fst (lookup K γ) ⟩
  arSubK-use x hxar = arityK (lookup ar γ) x hxar ?
