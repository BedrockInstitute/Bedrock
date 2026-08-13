{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.115] probe A: does someEnv build?  GREEN HALF.
--
-- someEnv is the one of the twenty-eight NEEDS NEW CONTENT facts
-- whose supplier is a CONSTRUCTION rather than a closure
-- (_build/lj-1.113-report.md section 3): an environment
--   E ∈ K-slot  ×  ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 ... ⟩
-- built from the three memberships ya yc ar ∈ K-slot
-- (src/L/Condensation/LowerAgree.lagda.md:51-58).
--
-- This probe attempts the construction generically at the K slot.
-- The attempt is the natural one: build the environment-set over the
-- arity (the machine's envSet machinery, L.Coding.EnvSet) and close
-- its membership in K.  The decisive question is which closure
-- properties of K the construction needs, because that decides
-- whether the closure family is 5 lemma shapes or 15.
--
-- The finding, machine-checked here:  the bounded half of the
-- obligation (envHypB2) is the delivered EnvSet.back transfer
-- (src/L/Condensation.lagda.md:2998-3000), wired at the And-row
-- layout in `build` below.  The construction half is ONE closure
-- property of K that nothing delivers:  the environment-set over an
-- ARBITRARY arity ar ∈ K with values in the ambient slot lies in K
-- (`EnvSetClosure`).  The delivered envSet builds only over a
-- numeral (src/L/Coding/EnvSet.lagda.md:183), and the only delivered
-- envSetAt-satisfaction supplier demands the arity slot equal # m
-- (src/L/Coding/Sound.lagda.md:262-284).  The refutation attempts
-- are probe B.
--
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ1115A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Coding.Model {ℓ}
  using ( envSetAt; envOverAt; prʟ; extAt-in-both )
open import L.Coding.EnvSet {ℓ} lem using ( envSet )
open import L.Condensation {ℓ} lem using ( envHypB2; module EnvSet )
open import L.Condensation.LowerAgree {ℓ} lem using ( someEnvDef )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )

open import Cubical.Data.Nat using ( _+_; ℕ )
open import Cubical.Data.FinData using ( Fin )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- The generic K slot: the someEnv obligation of the extended frame,
-- stated exactly as someEnvDef states it
-- (src/L/Condensation/LowerAgree.lagda.md:51-58).
module Obligation (n : ℕ) (K : Fin (5 + n)) (γ : S ^ (11 + n)) where

  KS : S
  KS = lookup (suc (suc (suc (suc (suc (suc K)))))) γ

  Obl : Type (ℓ-suc ℓ)
  Obl = (ya yc b a ar c : S) → ⟨ fst ya ∈ fst KS ⟩
      → ⟨ fst yc ∈ fst KS ⟩
      → ⟨ fst ar ∈ fst KS ⟩
      → Σ S (λ E → ⟨ fst E ∈ fst KS ⟩
        × ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 {11 + n} zero
             (suc (suc (suc (suc (suc (suc K)))))) ⟩)

  -- THE CONSTRUCTION'S NEEDED CLOSURE.  someEnv's E is the
  -- environment-set over the arity with values in the frame's B slot
  -- (the And/Or rows' ambient set, index 7 of the And-row list =
  -- lookup 0 γ).  The delivered envSet machinery builds that set
  -- over a NUMERAL arity only
  -- (L.Coding.EnvSet.lagda.md:183: envSet : (n : ℕ) → S).  The
  -- generic construction over an arbitrary arity ar ∈ K needs the
  -- set of environments over ar with values in the ambient slot to
  -- EXIST and lie in K, with the machine's envSetAt satisfaction at
  -- the And-row layout.  State it as a closure hypothesis.
  EnvSetClosure : Type (ℓ-suc ℓ)
  EnvSetClosure =
    (ar : S) → ⟨ fst ar ∈ fst KS ⟩
    → Σ S (λ E → ⟨ fst E ∈ fst KS ⟩
      × ((ya yc b a c : S) → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
           envSetAt zero (suc (suc (suc (suc (suc zero)))))
                     (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩))

  -- The two supplied companions of the transfer.
  -- arityK is a delivered KFacts field
  -- (src/L/Condensation.lagda.md:5974-5975); the frame derives its
  -- own from transK (src/L/Condensation/TwelveAgree.lagda.md:193-198).
  ArityK : Type (ℓ-suc ℓ)
  ArityK = (N v : S) → ⟨ fst v ∈ fst N ⟩
         → ⟨ fst N ∈ fst KS ⟩ → ⟨ fst v ∈ fst KS ⟩

  -- envInK at the And-row layout: the frame's envInK-imp shape
  -- (src/L/Condensation/TwelveAgree.lagda.md:137-140), one of the
  -- twenty-five closure facts.
  EnvInK : Type (ℓ-suc ℓ)
  EnvInK = (z E ya yc b a ar c : S)
         → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
              envOverAt zero (suc (suc (suc (suc (suc (suc zero))))))
                        (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ⟩
         → ⟨ fst z ∈ fst KS ⟩

  -- THE DECISIVE MINIATURE: with EnvSetClosure supplied, does the
  -- rest of someEnv build?  The bounded envHypB2 satisfaction is the
  -- EnvSet transfer of src/L/Condensation.lagda.md:2882 (back:
  -- envSetAt → envSetB under arityK, E∈K, ar∈K).  `build` wires
  -- that transfer at the And-row layout; the machine-side
  -- satisfaction comes from the closure.
  build : EnvSetClosure → ArityK → EnvInK → Obl
  build cl aK iK ya yc b a ar c yaK ycK arK =
    let (E , (EK , hAt)) = cl ar arK
        module A = EnvSet {18 + n}
          zero
          (suc (suc (suc (suc (suc zero)))))
          (suc (suc (suc (suc (suc (suc (suc zero)))))))
          (suc (suc (suc (suc (suc (suc (suc
                 (suc (suc (suc (suc (suc (suc K)))))))))))))
          (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
          aK EK arK (λ z → iK z E ya yc b a ar c)
    in E , (EK , A.back (hAt ya yc b a c))
