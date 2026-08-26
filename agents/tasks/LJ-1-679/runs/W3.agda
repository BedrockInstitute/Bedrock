{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.679] W3.  Does the bound live in Lset lam?  Two measurements,
-- neither a second formula.  Lands nothing in src/.
--
--   TAGS           the twelve numerals are members of the stage.
--                  Bound.num∈λ, not rebuilt (W2).
--   KVALUE         the tree's one KFacts value is Lset lam itself
--                  (src/L/Condensation.lagda.md:7369-7373).  That
--                  value is not a member of the stage: ∈-irrefl.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing is postulated.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-679.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.Coding.Bound {ℓ} lem using ( module Bound )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
open import Cubical.Data.Empty as Empty using ( ⊥ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- THE TREE'S KFacts SUPPLY IS THE STAGE, NOT A MEMBER OF THE STAGE.
kvalue-escapes : (lam : S) → ⟨ Lset lam ∈ˢ Lset lam ⟩ → Empty.⊥
kvalue-escapes lam = ∈-irrefl (Lset lam)

-- THE TWELVE TAGS DO LIVE IN THE STAGE.  W2: Bound.num∈λ, not a
-- second proof of numeral membership.
module Tags (lam : S) (ordλ : IsOrd lam)
            (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
            (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where
  module B = Bound lam ordλ succλ ∅∈λ

  tags-in-stage : (k : ℕ) → ⟨ fst (numeralL k) ∈ˢ Lset lam ⟩
  tags-in-stage = B.num∈λ
