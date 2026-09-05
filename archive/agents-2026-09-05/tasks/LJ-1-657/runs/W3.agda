{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.657]  W3, THE DECISIVE MINIATURE, TYPECHECKED ALONE.
--
--   The brief names the widest unmeasured term "the alphabet embedding
--   of premise 4" and estimates it at 80 to 170 lines.  The miniature
--   that settles it is TWO lines and it is a REFUTATION, not an
--   embedding: [LJ-1.653]'s `HoodExistsP` and `HoodSoundP`
--   (agents/tasks/LJ-1-653/Probe653.agda:283, :235) demand
--   `Formula (⊥* {ℓ-suc ℓ}) 2`, [LJ-1.650]'s `LevelFormula`
--   (agents/tasks/LJ-1-650/Probe650.agda:322-324) delivers
--   `Formula Code 2`, and relabelling out of `Code` needs
--   `Code → ⊥*`, which no `Code` inhabitant permits.
--
--   `wit` is a CONSTRUCTOR (src/L/Hull.lagda.md:72-74) and it asks only
--   for a parameter-free formula and a vector of codes, so `Code` is
--   inhabited with no hypothesis about `lam`, `X` or the hull at all.
--
--   Nothing is postulated.  No hole.  Nothing lands in src/.
--   ONE Agda process, caliber from the pane, never set here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-657.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( ⊤̇ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.Hull {ℓ} lem using ( module AtStage )

import Cubical.Data.Empty as Empty
open import Cubical.Data.Vec using ( [] )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ∅ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module W3 (lam : S) (ordλ : IsOrd lam)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module ASt = AtStage lam ordλ
  module H = ASt.Hull X X⊆L ∅∈λ
  module T = H.T

  code-inhabited : T.Code
  code-inhabited = T.wit 0 ⊤̇ []

  no-relabelling-out-of-Code : (T.Code → ⊥* {ℓ-suc ℓ}) → Empty.⊥
  no-relabelling-out-of-Code f = Empty.rec* (f code-inhabited)
