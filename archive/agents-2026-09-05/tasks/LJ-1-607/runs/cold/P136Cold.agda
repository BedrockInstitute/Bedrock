{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.607]  COLD RECHECK RUN.  Does [LJ-1.136]'s recorded cure
-- elaborate at TODAY's tree, from a cold cache?
--
-- The interface Agda holds for agents/tasks/LJ-1-136/ProbeLJ1136B.agda
-- was computed 2026-08-19 and merely VALIDATED by the warm run
-- (runs/p136-2.out).  Validation is not re-elaboration: the tree has
-- moved since 19 Aug.  So the two probe files are copied VERBATIM into
-- this directory (same module names, so the imports resolve at this
-- local include root) and this checker re-ascribes the cure against a
-- FRESH interface namespace.  What this run elaborates, it elaborates
-- at today's sources.
--
-- CAP 600 s, GHCRTS as the program set it (-A64m -I0 -M2g), one Agda
-- process.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import FOL.ZFStructure using ( module hPropStructure )

module P136Cold {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

  open import L.Constructible {ℓ} using ( IsOrd; 𝒮ʟ )
  open hPropStructure 𝒮ʟ using ( S )
  open import ProbeLJ1136B lem

  module At (β : V ℓ) (oβ : IsOrd β) (D C : S) where

    open Sel β oβ D C

    -- 1.  THE TERM [LJ-1.114] COULD NOT WRITE, re-ascribed cold: the
    --     L-least selection does not depend on which proof of
    --     non-emptiness reached it.
    pick-canonical-cold : (h₁ h₂ : Ne) → pick h₁ ≡ pick h₂
    pick-canonical-cold = pick-canonical

    -- 2.  THE DISCHARGE, re-ascribed cold: from the TRUNCATED
    --     existence of a constructible injective graph, an HONEST
    --     injection between the small index types.
    discharge-cold :
        Ne → Σ[ f ∈ (⟪ fst D ⟫ → ⟪ fst C ⟫) ]
               ((m n : ⟪ fst D ⟫) → f m ≡ f n → m ≡ n)
    discharge-cold = discharge
