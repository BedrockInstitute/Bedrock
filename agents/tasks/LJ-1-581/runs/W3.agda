{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.581] W3.  THE PAIRS OF κ, AS AN L-SET WITH ITS TWO PROJECTIONS.
--
-- WRITTEN FIRST AND TYPECHECKED ALONE, before any other Agda of this
-- task, exactly as the brief orders.  No hole, no postulate.
--
-- The brief names the widest unmeasured term:
--
--     -- the pairs of κ, as an L-SET with its two projections, TYPE ONLY
--
-- and attaches one question to it: "[LJ-1.556] reports its section 1
-- delivers the product and its two readings; CHECK WHETHER THAT IS THE
-- SAME OBJECT before you build anything on top of it."
--
-- So this slice writes the TYPE first, in the ambient pairing `pr` and
-- with both components as INDICES, and then answers the attached
-- question the only way it can be answered: by inhabiting that type
-- from [LJ-1.556]'s section 1 alone.  `PairsOf` is new here; its
-- inhabitant is NOT.  Nothing below builds a set.
--
-- THE DOMAIN IS NOT REBUILT HERE.  It is imported from [LJ-1.556]'s
-- probe, agents/tasks/LJ-1-556/Probe556.agda:148 (`sqL`), :156
-- (`sqL-in`) and :186 (`sqL-out`), which are green and tracked, and
-- which [LJ-1.567] already imported the same way
-- (agents/tasks/LJ-1-567/runs/W3.agda:22-25).
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M8g" on this pane.  I
-- did not set it.  One Agda process at a time.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-581.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Coding.Model {ℓ} using ( prʟ-fst )

import LJ-1-556.Probe556 {ℓ} lem as P556

open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

-- THE TYPE.  "P is the pairs of κ, as an L-set, with its two
-- projections."  Reading one puts every ambient pair of two members of
-- κ inside P.  Reading two takes a member of P back to the two INDICES
-- it is the pair of, and it is UNTRUNCATED, which is what a consumer
-- that wants the components as data needs.
PairsOf : S → Type (ℓ-suc ℓ)
PairsOf κ =
  Σ[ P ∈ S ]
    ( ((m n : ⟪ fst κ ⟫) → ⟨ pr (⟪ fst κ ⟫↪ m) (⟪ fst κ ⟫↪ n) ∈ fst P ⟩)
    × ((z : S) → ⟨ fst z ∈ fst P ⟩
       → Σ[ p ∈ (⟪ fst κ ⟫ × ⟪ fst κ ⟫) ]
           (fst z ≡ pr (⟪ fst κ ⟫↪ (fst p)) (⟪ fst κ ⟫↪ (snd p)))) )

-- THE ANSWER.  [LJ-1.556]'s section 1 IS this object.  The only thing
-- that had to be checked is the bridge `prʟ-fst`
-- (src/L/Coding/Model.lagda.md:329): section 1 states both readings at
-- the L-pair `prʟ`, and this type states them at the ambient pair `pr`.
same-object : (κ : S) → PairsOf κ
same-object κ = Sq.sqL , inward , outward
  where
  module Sq = P556.Square κ

  inward : (m n : ⟪ fst κ ⟫)
         → ⟨ pr (⟪ fst κ ⟫↪ m) (⟪ fst κ ⟫↪ n) ∈ fst Sq.sqL ⟩
  inward m n = subst (λ w → ⟨ w ∈ fst Sq.sqL ⟩)
                 (prʟ-fst (Sq.toκ m) (Sq.toκ n)) (Sq.sqL-in m n)

  outward : (z : S) → ⟨ fst z ∈ fst Sq.sqL ⟩
          → Σ[ p ∈ (⟪ fst κ ⟫ × ⟪ fst κ ⟫) ]
              (fst z ≡ pr (⟪ fst κ ⟫↪ (fst p)) (⟪ fst κ ⟫↪ (snd p)))
  outward z h = Sq.sqL-out z h .fst
              , Sq.sqL-out z h .snd
              ∙ prʟ-fst (Sq.toκ (Sq.sqL-out z h .fst .fst))
                        (Sq.toκ (Sq.sqL-out z h .fst .snd))
