{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.647]  W3 PROBE.  The widest unmeasured term, measured.
--
-- THE BRIEF NAMES W3 AS "the `Formula Code 1` that `hull-closed` needs,
-- built from the keystone's `d`", at 70 to 150 lines.  This probe asks
-- the prior question the brief's premise 2 assumes away: does step 2
-- need `hull-closed` AT ALL?
--
-- Premise 2 says `hull-closed` (src/L/Hull.lagda.md:415) is the hull's
-- ONLY closure rule.  It is not.  `inHull` (src/L/Hull.lagda.md:344,
-- `val-in-Hull c = inHull c`) puts the value of ANY code in the hull
-- with no formula, and `hull-member` (:337-339) reads a member back AS
-- a code, by `x∈H` itself and not by a proof.  So the hull's membership
-- IS "is the value of a code", and a hypothesis that PRODUCES a code
-- discharges closure directly.
--
-- If this file is green, the W3 term is ZERO lines of `Formula Code 1`
-- and the brief's 70-to-150 estimate is refuted downward.
--
-- Nothing is postulated.  Nothing lands in src/.
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-647.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.Hull {ℓ} lem using ( module AtStage )

open import Cubical.Data.Sigma using ( Σ-syntax )
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module HullStage (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module ASt = AtStage lam ordλ
  module H = ASt.Hull X X⊆L ∅∈λ

  M : S
  M = H.T.Hull

  open H.T using ( Code; val )

  LsetCodeOrd : Type (ℓ-suc ℓ)
  LsetCodeOrd =
    (c : Code) → IsOrd (fst (val c))
    → Σ[ d ∈ Code ] (fst (val d) ≡ Lset (fst (val c)))

  -- THE ROUTE, WITH NO FORMULA ANYWHERE.
  hull-closed-lset : LsetCodeOrd
                   → (y : S) → ⟨ y ∈ˢ M ⟩ → IsOrd y → ⟨ Lset y ∈ˢ M ⟩
  hull-closed-lset lco y y∈M ordy =
    PT.rec (snd (Lset y ∈ˢ M)) go (H.hull-member y y∈M)
    where
    go : Σ[ c ∈ Code ] (fst (val c) ≡ y) → ⟨ Lset y ∈ˢ M ⟩
    go (c , q) =
      let ordc : IsOrd (fst (val c))
          ordc = subst IsOrd (sym q) ordy
          dq : Σ[ d ∈ Code ] (fst (val d) ≡ Lset (fst (val c)))
          dq = lco c ordc
      in subst (λ z → ⟨ z ∈ˢ M ⟩)
               (snd dq ∙ cong Lset q)
               (H.val-in-Hull (fst dq))
