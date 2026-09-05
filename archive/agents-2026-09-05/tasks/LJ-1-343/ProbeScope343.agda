{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.343] THE ONE PREMISE THE FIVE-LINE ESTIMATE RESTS ON.
--
-- The brief says the repaired hypothesis is FREE at the call sites,
-- because `hz` is already bound at src/L/Condensation.lagda.md:6799 and
-- :6814.  `[LJ-1.341]` read that from two line numbers and landed no
-- repair, so this file MEASURES it before any chapter run.
--
-- `hz` has the SATISFACTION type
--     < (z : g) |= (var zero in var (suc w)) >
-- because it is the first conjunct of `bodyB` (:6791) and `bodyM`
-- (:6795).  The repaired hypothesis wants the SET type
--     < fst z in fst (lookup w g) >.
-- If the two are not the same type up to unfolding, the repair needs a
-- transport at each of three call sites and the estimate is wrong.
--
-- THE TEST IS THE IDENTITY FUNCTION.  If `λ x → x` typechecks in both
-- directions, `hz` is usable with no transport at all.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; ∃̇_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

module LJ-1-343.ProbeScope343 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import L.Constructible {ℓ} using ( 𝒮ʟ )

import L.Coding.Model
module GM = L.Coding.Model {ℓ}
open GM.AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

open import L.Coding.Powerset {ℓ} lem using ( envOneAt )

open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- PART 1.  `hz` IS THE SET MEMBERSHIP, WITH NO TRANSPORT.
--
-- The shape is `DefinesAgree`'s own, src/L/Condensation.lagda.md:6778:
-- the carrier slot is the parameter `w`, the environment is `γ`, and the
-- body is read at `z ∷ γ`.
-- =====================================================================

module Scope {m : ℕ} (w : Fin m) (γ : S ^ m) where

  -- The first conjunct of `bodyB` (:6791) and of `bodyM` (:6795).
  carrierFo : Formula S (suc m)
  carrierFo = var zero ∈̇ var (suc w)

  -- FORWARD.  The satisfaction hypothesis IS the set membership.
  hz-is-member : (z : S) → ⟨ (z ∷ γ) ⊨ carrierFo ⟩
               → ⟨ fst z ∈ fst (lookup w γ) ⟩
  hz-is-member z hz = hz

  -- BACKWARD.  And the other way, so the two types are the same type.
  member-is-hz : (z : S) → ⟨ fst z ∈ fst (lookup w γ) ⟩
               → ⟨ (z ∷ γ) ⊨ carrierFo ⟩
  member-is-hz z hz = hz

-- =====================================================================
-- PART 2.  THE REPAIRED TELESCOPE, AT THE CHAPTER'S OWN SHAPE, AND THE
-- THREE CALL SITES FED FROM `hz` ALONE.
--
-- This restates `DefinesAgree`'s two repaired parameters and shows that
-- a clause which destructures `bodyB` can feed BOTH of them with the
-- `hz` it already has.  Nothing else is passed.
-- =====================================================================

module Feed {m : ℕ} (w K : Fin m) (γ : S ^ m)
  (envK : (E z : S) → ⟨ fst z ∈ fst (lookup w γ) ⟩
         → ⟨ (E ∷ z ∷ γ) ⊨ envOneAt zero (suc zero) ⟩
         → ⟨ fst E ∈ fst (lookup K γ) ⟩)
  (pairK : (E z w' : S) → ⟨ fst z ∈ fst (lookup w γ) ⟩
          → ⟨ (w' ∷ E ∷ z ∷ γ) ⊨ GM.tagAtL zero 0 (suc (suc zero)) ⟩
          → ⟨ fst w' ∈ fst (lookup K γ) ⟩) where

  bodyM : Formula S (suc m)
  bodyM = (var zero ∈̇ var (suc w))
          ∧̇ ∃̇ (envOneAt zero (suc zero) ∧̇ (var zero ∈̇ var (suc (suc w))))

  -- The `:6820` site: `envK E z hE` becomes `envK E z hz hE`.
  feedEnvK : (z : S) → ⟨ (z ∷ γ) ⊨ bodyM ⟩ → (E : S)
           → ⟨ (E ∷ z ∷ γ) ⊨ envOneAt zero (suc zero) ⟩
           → ⟨ fst E ∈ fst (lookup K γ) ⟩
  feedEnvK z (hz , _) E hE = envK E z hz hE

  -- The `:6811` and `:6826` sites: the lambda handed to `EnvOneAgree`
  -- gains one argument and nothing else.
  feedPairK : (z : S) → ⟨ (z ∷ γ) ⊨ bodyM ⟩ → (E : S)
            → ((w' : S) → ⟨ (w' ∷ E ∷ z ∷ γ) ⊨ GM.tagAtL zero 0 (suc (suc zero)) ⟩
                        → ⟨ fst w' ∈ fst (lookup K γ) ⟩)
  feedPairK z (hz , _) E = λ w' hw → pairK E z w' hz hw
