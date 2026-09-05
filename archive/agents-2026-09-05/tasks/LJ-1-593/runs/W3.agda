{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.593] W3.  THE PAIRS OF KAPPA AS AN L-SET, AT THIS SPELLING.
-- TYPE ONLY.
--
-- WRITTEN FIRST AND TYPECHECKED ALONE, before any other Agda of this
-- task, exactly as the brief orders.  No hole, no postulate.
--
-- The brief names the widest unmeasured term:
--
--     -- the pairs of κ, as an L-SET, under the three hypotheses,
--     -- TYPE ONLY
--
-- THE THREE HYPOTHESES ARE [LJ-1.589]'s, and they are copied from the
-- row that now carries them: `SuccIntoPowerInf`
-- (agents/tasks/LJ-1-589/Probe589.agda:243-247) binds `IsOrd (fst κ)`,
-- `IsCardinalL κ` and `ClauseTrophy κ`, and `ClauseTrophy` is
-- `(⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)` (Probe589.agda:96-97), which is
-- `GCHStatement`'s fourth hypothesis (src/L/GCH.lagda.md:64) copied
-- letter for letter.
--
-- NOTHING IS IMPORTED FROM A PREDECESSOR PROBE.  The object is written
-- from `src/` alone, so this slice measures the SHAPE at the three
-- hypotheses and not [LJ-1.556]'s import cost.  Whether the shape is
-- the SAME OBJECT as [LJ-1.556]'s `Square.sqL` is a question about a
-- term and not about a type, so it belongs in the probe and not here.
--
-- WHAT THE SLICE ASKS.  Can the pairs of kappa be NAMED as an L-set,
-- with both readings, under exactly these three hypotheses and no
-- other?  It builds nothing and it inhabits nothing.
--
-- CALIBER.  The program set GHCRTS on this pane.  I did not set it.
-- One Agda process at a time.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-593.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL-trans; IsOrd )
open import L.Cardinal {ℓ} lem using ( IsCardinalL )
open import L.Coding.Model {ℓ} using ( prʟ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- Every member of kappa, as an element of L.  Three lines, and they
-- are [LJ-1.556]'s `toκ` (agents/tasks/LJ-1-556/Probe556.agda:96-98)
-- rewritten from `src/` rather than imported.
toκ : (κ : S) → ⟪ fst κ ⟫ → S
toκ κ m = ⟪ fst κ ⟫↪ m
        , isL-trans {x = fst κ} {y = ⟪ fst κ ⟫↪ m} (member (fst κ) m) (snd κ)

-- THE PAIRS OF KAPPA AS AN L-SET, WITH BOTH READINGS.  `P` is the set;
-- the second field says every coded pair of two members of kappa is a
-- member of it; the third says every member of it is such a pair.
Pairs : S → Type (ℓ-suc ℓ)
Pairs κ =
  Σ[ P ∈ S ]
    ( ((m n : ⟪ fst κ ⟫) → ⟨ fst (prʟ (toκ κ m) (toκ κ n)) ∈ fst P ⟩)
    × ((z : S) → ⟨ fst z ∈ fst P ⟩
       → Σ[ p ∈ ⟪ fst κ ⟫ × ⟪ fst κ ⟫ ]
           (fst z ≡ fst (prʟ (toκ κ (fst p)) (toκ κ (snd p))))) )

-- THE WIDEST UNMEASURED TERM, AT THE THREE HYPOTHESES.  TYPE ONLY.
PairsAtSpelling : Type (ℓ-suc ℓ)
PairsAtSpelling =
    (κ : S) → IsOrd (fst κ) → IsCardinalL κ → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → Pairs κ

-- AND THE OBJECT DOES NOT DEPEND ON ANY OF THE THREE.  If the pairs
-- can be named at no hypothesis at all, then they can be named at
-- these three, and the narrowing costs nothing.  TYPE ONLY: this says
-- one type pays the other, and neither is inhabited here.
PairsUnconditional : Type (ℓ-suc ℓ)
PairsUnconditional = (κ : S) → Pairs κ

unconditional-pays : PairsUnconditional → PairsAtSpelling
unconditional-pays f κ _ _ _ = f κ
