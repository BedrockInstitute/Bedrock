{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.743] PROBE.  Lset-trans-set, the name the meter reads.  The
--                   obligation is 725-SPLIT's inhabited transitivity
--                   re-exported at its own top-level name in a fresh
--                   file, because the live meter has no obligation
--                   named Lset-trans-set (supply 0 at dispatch) and a
--                   nested or sibling name is not the meter name
--                   ([LJ-1.734] precedent).  Lands nothing in src/.
--
--   OBLIGATION  Lset-trans-set:  members of members of Lset gamma lie
--               in Lset gamma.  Transcribed from the bytes that
--               typechecked at agents/tasks/LJ-1-725-SPLIT/
--               Probe725Split.agda:71-79 (that probe's verdict run
--               p-8 was EXIT=0 at 1.77 s).  The predecessor's report
--               verdict is GO on this term and STOP on the separate
--               type stage-read; this file does NOT state or inhabit
--               stage-read, and no postulate stands anywhere.
--   DELIVERED   Lset-trans-set, stated and INHABITED at the file's
--               top level, over the landed readings Lset-out,
--               D-o-membership refinement and Lset-mono.  Nothing
--               else: no iterate, no second section.  The two-step
--               iterate the spine consumes is two applications of
--               this name (725-SPLIT's Lset-trans-set^2 at
--               Probe725Split.agda:84-88), not new content here.
--
-- The import cone is TRIMMED against 725-SPLIT's frame: that file
-- also carried stage-read's Relativize, Absoluteness, Syntax,
-- Ordinal, Stages, Axioms and Coding imports and its LEM parameter;
-- none of them is used by this term.  Every partial import pulled
-- facts its own rows never used ([LJ-1.559]/[LJ-1.566] pattern), so
-- the trimmed floor was priced before the proof was attempted.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and untouched here.

open import Base.Prelude
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

module LJ-1-743.Probe743 {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
import Cubical.HITs.PropositionalTruncation as PT
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( Lset; Lset-mono; Lset-out; 𝒟ₒ; 𝒟ₒ∋⊆ )
open hPropStructure 𝒮ᵥ using () renaming ( _∈ˢ_ to _∈ˢᵥ_ )

-- =====================================================================
-- Lset-trans-set.  Members of members of Lset γ lie in Lset γ.  The
-- content is the landed refinement of the operator (a member of D-o A
-- never has a member outside A) plus monotonicity:  one PT.rec over
-- Lset-out, closed by D-o∋⊆ and Lset-mono.  Bytes identical to
-- Probe725Split.agda:71-79;  only the surrounding file is new.
-- =====================================================================

Lset-trans-set : (γ a x : V ℓ)
               → ⟨ a ∈ˢᵥ x ⟩ → ⟨ x ∈ˢᵥ Lset γ ⟩ → ⟨ a ∈ˢᵥ Lset γ ⟩
Lset-trans-set γ a x a∈ x∈ = PT.rec (snd (a ∈ˢᵥ Lset γ)) step (Lset-out γ x x∈)
  where
  step : Σ[ δ ∈ V ℓ ] (⟨ δ ∈ˢᵥ γ ⟩ × ⟨ x ∈ˢᵥ 𝒟ₒ (Lset δ) ⟩)
       → ⟨ a ∈ˢᵥ Lset γ ⟩
  step (δ , (δ∈γ , x∈𝒟)) =
    Lset-mono {α = γ} {β = δ} δ∈γ {x = a}
      (𝒟ₒ∋⊆ (Lset δ) x x∈𝒟 a a∈)
