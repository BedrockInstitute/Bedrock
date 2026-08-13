{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.49 probe A: the landed cure 1, measured at the CONSUMER'S own
-- objects.  `DefBodyB` (the leaf inside the bounded graph) and
-- `LevelHood0.matrix` (the level-hood matrix at n = 0) are now
-- constant-free: countFo is zero by refl, Cnt.erase applies, and the
-- Delta-0 certificate rides the erasure (erase-Delta-0).

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ149 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Δ₀ )
open import FOL.Manipulation.Parameters using ( countFo )
open import FOL.Manipulation.Relabelling using ( embed )
import FOL.Count
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; Lset )
open import L.Condensation {ℓ} lem using ( DefBodyB; Δ₀-DefBodyB )
open import L.BoundedSubset {ℓ} lem using ( module LevelHood0; erase-Δ₀ )
open import L.Hull {ℓ} lem using ( module AtStage )
open import Cubical.Data.Vec using ( Vec; _∷_; [] )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ∅ )

open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

module Cnt = FOL.Count.Count {ℓ = ℓ-suc ℓ} CS.S

-- The leaf at n = 0, arity 8, all sixteen slots at zero.
defb : Formula CS.S 8
defb = DefBodyB {0}
  zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero

count-defb : countFo defb ≡ 0
count-defb = refl

erased-defb : Formula (⊥* {ℓ-suc ℓ}) 8
erased-defb = Cnt.erase defb refl

module LH0 = LevelHood0
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero
  zero zero zero zero zero zero zero zero zero zero zero zero zero zero

-- The level-hood matrix itself, at n = 0.
count-matrix : countFo LH0.matrix ≡ 0
count-matrix = refl

erased-matrix : Formula (⊥* {ℓ-suc ℓ}) 4
erased-matrix = Cnt.erase LH0.matrix refl

-- The level-hood statement at the hull's carrier: the Sigma-2 form is
-- constant-free, so it embeds to ANY carrier without a placement (P-u).
count-sigma2 : countFo LH0.Σ₂ ≡ 0
count-sigma2 = refl

-- The same statement as a `Formula Code 1` at the hull of a stage: the
-- erase/embed route needs no constants and no placement.
module HullPack (α : S) (ordα : IsOrd α) (X : S)
  (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset α ⟩) (∅∈α : ⟨ ∅ ∈ˢ α ⟩) where
  module ASt = AtStage α ordα
  module H = ASt.Hull X X⊆L ∅∈α

  -- the level-hood statement at the hull, with the ordinal parameter free
  atHull : Formula H.T.Code 1
  atHull = embed (Cnt.erase LH0.Σ₂ refl)

  count-atHull : countFo atHull ≡ 0
  count-atHull = refl
