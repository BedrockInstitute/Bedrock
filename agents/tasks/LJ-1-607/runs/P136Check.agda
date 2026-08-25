{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.607]  RUN, NOT A DELIVERABLE ROW.  D-10: does the recorded
-- cure of [LJ-1.136] still elaborate at TODAY's tree?
--
-- The brief's premise: "`pick-canonical` ... exists in no Agda
-- anywhere: not in `src/`, not in `archive/src/`, only as that one
-- name in the index."  That grep missed the probes' home: the library
-- file puts `agents/tasks` on the include path (bedrock.agda-lib,
-- `include: src agents/tasks`), and the term lives at
-- agents/tasks/LJ-1-136/ProbeLJ1136B.agda:114.  This file measures
-- whether it still TYPECHECKS here, at the tree this dispatch stands
-- on, by re-ascribing both halves of the cure (`pick-canonical` and
-- `discharge`) at a stage, a domain and a range of the Sel module's
-- own choosing.
--
-- CAP 600 s.  One Agda process.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import FOL.ZFStructure using ( module hPropStructure )

module LJ-1-607.runs.P136Check {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

  open import L.Constructible {ℓ} using ( IsOrd; 𝒮ʟ )
  open hPropStructure 𝒮ʟ using ( S )
  open import ProbeLJ1136B lem

  module At (β : V ℓ) (oβ : IsOrd β) (D C : S) where

    open Sel β oβ D C

    -- 1.  THE TERM [LJ-1.114] COULD NOT WRITE, re-ascribed at today's
    --     tree: the L-least selection does not depend on which proof
    --     of non-emptiness reached it.
    pick-canonical-survives : (h₁ h₂ : Ne) → pick h₁ ≡ pick h₂
    pick-canonical-survives = pick-canonical

    -- 2.  THE DISCHARGE, re-ascribed: from the TRUNCATED existence of
    --     a constructible injective graph, an HONEST injection between
    --     the small index types.  No truncation left over.
    discharge-survives :
        Ne → Σ[ f ∈ (⟪ fst D ⟫ → ⟪ fst C ⟫) ]
               ((m n : ⟪ fst D ⟫) → f m ≡ f n → m ≡ n)
    discharge-survives = discharge
