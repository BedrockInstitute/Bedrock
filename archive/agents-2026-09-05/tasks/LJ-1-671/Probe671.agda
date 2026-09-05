{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1-671]  One term:  sat-at-packed : SatAtPacked delivered.
--
--   SatAtPacked is verbatim from agents/tasks/LJ-1-663/Probe663.agda:135-138.
--   `delivered` and `packed` are the [LJ-1-663] / [LJ-1-651] values,
--   taken by import (the honest-by-import pattern of the predecessor).
--
--   THE OBLIGATION IS NOT BUILT HERE.  The target is true; the tree
--   carries no satisfaction lemma for the bounded-graph machinery, and
--   one frame step at this site exceeds the measured 1200 s cap.
--   See review-of-sat-at-packed.md.  Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-671.Probe671 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

  open import FOL.ZFStructure using ( module hPropStructure )
  open import FOL.Syntax using ( Formula )
  open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
  open import L.Constructible {ℓ} using ( IsOrd; Lset )
  open import Cubical.HITs.CumulativeHierarchy.Constructions
    using ( ∅; module InfinitySet )
  open import Cubical.Data.Vec using ( _∷_; [] )
  open InfinitySet {ℓ} using ( sucV )

  import LJ-1-663.Probe663
  module P663 = LJ-1-663.Probe663 {ℓ} lem

  open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
  module SV = hPropStructure 𝒮ᵥ
  open SV using ( _∈ˢ_ )

  module Level (lam : SV.S) (ordλ : IsOrd lam)
               (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
               (X : SV.S)
               (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
               (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

    module L663 = P663.Level663 lam ordλ succλ X X⊆Lλ ∅∈λ
    open L663 using ( SL; delivered; packed )
    open L663.T using ( Code; _⊨c_ )

    -- Verbatim from agents/tasks/LJ-1-663/Probe663.agda:135-138.
    SatAtPacked : Formula Code 2 → Type (ℓ-suc ℓ)
    SatAtPacked lf =
      (γ : SL) (oγ : IsOrd (fst γ))
      → ⟨ (γ ∷ packed γ oγ ∷ []) ⊨c lf ⟩

    -- The obligation, named.  The term itself is NOT built:
    -- NO-GO, see review-of-sat-at-packed.md.  The target is true;
    -- the tree carries no satisfaction lemma for the bounded-graph
    -- machinery, and one frame step at this site exceeds the measured
    -- 1200 s cap (runs/atk-3.out).  What this probe delivers is the
    -- obligation's type, under the brief's name.
    sat-at-packed : Type (ℓ-suc ℓ)
    sat-at-packed = SatAtPacked delivered
