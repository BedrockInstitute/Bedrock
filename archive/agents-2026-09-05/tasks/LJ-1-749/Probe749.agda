{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.749] PROBE.  prʟ-in-Lset-lim at the top-level name the brief
-- names:  the L-PRESENTATION of the V-pair leaf [LJ-1.748] delivered.
-- prʟ-fst (src/L/Coding/Model.lagda.md:329) reads fst (prʟ a b) back as
-- pr (fst a) (fst b), so the obligation is 748's pr-in-Lset-lim carried
-- across one subst along prʟ-fst.  Lands nothing in src/.
--
--   THE OBLIGATION   prʟ-in-Lset-lim.  The pair CODE prʟ a b has
--                    fst (prʟ a b) in Lset γ as soon as fst a and fst b
--                    both are.  NOT pair-in-Lγω and NOT table-sat:
--                    neither name occurs in this file outside comments.
--   SUPPLY USED      pr-in-Lset-lim is IMPORTED from [LJ-1.748]'s probe
--                    (agents/tasks/LJ-1-748/Probe748.agda:132), not
--                    transcribed: bedrock.agda-lib carries agents/tasks
--                    as an include root, so the predecessor probe is a
--                    module.  The src Bound wrapper's ∅∈λ wall never
--                    appears here: 748 already carried the transcription
--                    on its side of the import.
--   W3               the brief asks whether subst along prʟ-fst converts
--                    on 748's term.  MEASURED: no conversion is needed
--                    for the typecheck (subst's declared endpoint type is
--                    the goal itself, so the application elaborates
--                    without prʟ-fst reducing to refl); see the report.
--   FLOOR            the file first checked with {!floor!} standing in
--                    for the body, to price the elaboration frame
--                    (floor-first law); see runs/floor-1.*.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-749.Probe749 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import L.Constructible {ℓ} using ( IsOrd; Lset; 𝒮ʟ )
open import L.Ordinal.StageArith {ℓ} lem using ( closedω )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst )
open import LJ-1-748.Probe748 {ℓ} lem using ( pr-in-Lset-lim )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
-- The V open supplies ∈ˢ at V (the statement's membership); its own S
-- (= V ℓ) is hidden so that the L carrier S (𝒮ʟ's Σ over isL) is the
-- unambiguous S the obligation reads.
open hPropStructure 𝒮ᵥ hiding ( S )
open hPropStructure 𝒮ʟ using ( S )

------------------------------------------------------------------------------
-- THE OBLIGATION.  748's V-pair leaf, read through prʟ-fst: transport
-- pr (fst a) (fst b) ∈ˢ Lset γ back along sym (prʟ-fst a b).

prʟ-in-Lset-lim :
    (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
    (a b : S)
    → ⟨ fst a ∈ˢ Lset γ ⟩ → ⟨ fst b ∈ˢ Lset γ ⟩
    → ⟨ fst (prʟ a b) ∈ˢ Lset γ ⟩
prʟ-in-Lset-lim γ oγ clγ a b ha hb =
  subst (λ w → ⟨ w ∈ˢ Lset γ ⟩) (sym (prʟ-fst a b))
    (pr-in-Lset-lim γ oγ clγ (fst a) (fst b) ha hb)
