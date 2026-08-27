{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.699] PROBE.  The equivalence, both directions, with its real
-- bill.  The forward direction is SUPPLIED FROM [LJ-1.690], whose probe
-- is in this worktree and is imported.  The reverse direction was
-- DELIVERED BY [LJ-1.685], whose probe is in the SIBLING worktree
-- LJ-1-685 and is not on this worktree's include path: it cannot be
-- imported here.  So this probe states the union of the two
-- directions' hypotheses, supplies the forward conjunct, and names the
-- reverse conjunct as a type that is not inhabited.  The paired term
-- same-as-graph-both is therefore NOT written: its reverse half would
-- have to import [LJ-1.685].  The review states the NO-GO.
-- Lands nothing in src/.
--
--   W3              whether the two telescopes meet without a third
--                   bridge.  Measured at the frame
--                   (runs/FLOOR.agda.txt) and at the forward half here.
--   THE OBLIGATION  same-as-graph-both.  Not written: the reverse
--                   conjunct is in the sibling worktree.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.
-- Nothing is postulated.  No hole in this file.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-699.Probe699 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

  open import FOL.ZFStructure using ( module hPropStructure )
  import FOL.Absoluteness
  open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
  open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
  open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
  open import Cubical.Data.Vec using ( lookup )
  open import Cubical.Data.Nat using ( _+_ )

  import LJ-1-520.Probe520 {ℓ} lem as P520
  import LJ-1-690.Probe690 {ℓ} lem as P690

  open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
  open hPropStructure 𝒮ʟ
  module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
  open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

  -- W2: the union of the two directions' hypotheses, written once at a
  -- generic arity and generic slots, and instantiated by each conjunct.
  -- The forward's three are the predecessor [LJ-1.690]'s own (PowIterHyp,
  -- IsOrd at the k-value, the UP bridge).  The reverse's bridge is the
  -- DOWN bridge, restated because [LJ-1.685] is not importable here.
  module At {n : ℕ} (w b : Fin n) (γ : S ^ n) where
    module Sl   = P520.Slots w b
    module Mx   = Sl.Mx
    module FPin = P690.Pin {n} w b γ
    private
      M : ℕ
      M = 13 + n

      sh13 : Fin n → Fin M
      sh13 i = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (i)))))))))))))

    -- THE FORWARD CONJUNCT, SUPPLIED FROM [LJ-1.690].  The predecessor's
    -- own term, at this carrier.  Sigma-1 to graph.
    same-as-graph-forward :
      P690.PowIterHyp →
      IsOrd (fst (lookup b γ)) →
      FPin.Bridge →
      ⟨ γ ⊨ fst (P520.levelFo-Σ₁ w b) ⟩ →
      ⟨ γ ⊨ LsetGraphAt w b ⟩
    same-as-graph-forward = FPin.same-as-graph-forward-at

    -- [LJ-1.685]'s Bridge, DOWN, at one environment (sibling
    -- Probe685.agda:66-69).  The type the reverse delivered, restated
    -- by hand because the module is not on this include path.
    Bridge-DOWN : Type (ℓ-suc ℓ)
    Bridge-DOWN = (δ : S ^ M)
               → ⟨ δ ⊨ LsetGraphAt (sh13 w) (sh13 b) ⟩
               → ⟨ δ ⊨ Mx.G.graphBndAt ⟩

    -- THE REVERSE CONJUNCT, DELIVERED BY [LJ-1.685] (sibling
    -- Probe685.agda:66-76), graph to Sigma-1.  Its DOWN bridge and its
    -- IsOrd spend are the predecessor's own type, restated here.
    -- Named, not inhabited: the term lives in the sibling worktree.
    same-as-graph-reverse : Type (ℓ-suc ℓ)
    same-as-graph-reverse =
      P690.PowIterHyp →
      IsOrd (fst (lookup b γ)) →
      Bridge-DOWN →
      ⟨ γ ⊨ LsetGraphAt w b ⟩ →
      ⟨ γ ⊨ fst (P520.levelFo-Σ₁ w b) ⟩

    -- WHAT THE OBLIGATION ASKS, AND WHY IT IS NOT WRITTEN.  The pair of
    -- the two conjuncts, at the union of their hypotheses:
    --
    --   same-as-graph-both :
    --     P690.PowIterHyp → IsOrd (fst (lookup b γ))
    --     → FPin.Bridge → Bridge-DOWN → P520.SameAsGraph w b γ
    --   same-as-graph-both p o up down =
    --     ( same-as-graph-forward p o up
    --     , (same-as-graph-reverse) p o down )
    --
    -- The second component is a value of same-as-graph-reverse, which
    -- only [LJ-1.685] can supply, and it is in the sibling worktree.
    -- See review-of-same-as-graph-both.md.
