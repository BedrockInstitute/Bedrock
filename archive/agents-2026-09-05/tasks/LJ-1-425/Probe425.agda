{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.425] PROBE.  Unlock InternalLeastCard.Selected's one hypothesis.
-- Lands nothing in src/.
--
--   W3 FIRST  `graph-in-site-bound`.  The membership
--             ⟨ fst G ∈ˢ Lset β ⟩, with G a bare module hypothesis
--             and nothing carved, before InclGraph is applied.
--             The inhabitant is the Lset-mono / stage-mem composition.
--             Its premise is the missing comparison: the graph's
--             stage under the site bound.  The tree delivers none.
--
--   TERM      `internal-nonempty`.  Selected's one hypothesis, Good
--             unfolded.  Generic in κ with oκ as module parameter.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-425.Probe425 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; IsOrd; Lset; Lset-mono )
open import L.Stage {ℓ} lem using ( stage; stage-mem )
open import L.Choice.Stage {ℓ} lem using ( stageBound )
open import L.Choice.Step {ℓ} lem using ( Mem )
open import L.Cardinal {ℓ} lem using ( InjCode; module SiteBound )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- W3.  G is a bare module hypothesis.  Nothing is carved.
-- Checking this module measures graph-in-site-bound.
-- =====================================================================

module GraphInSite (κ : S) (oκ : IsOrd (fst κ)) (G : S) where

  open SiteBound κ

  graph-in-site-bound :
      ⟨ stage (fst G) (snd G) ∈ˢ β ⟩
    → ⟨ fst G ∈ˢ Lset β ⟩
  graph-in-site-bound stg∈β =
    Lset-mono {α = β} {β = stage (fst G) (snd G)}
      stg∈β (stage-mem (fst G) (snd G))

-- =====================================================================
-- κ's membership.  The site bound contains the set's own stage, so
-- Lset-mono and stage-mem close it.  That comparison is delivered.
-- =====================================================================

module KappaInSite (κ : S) (oκ : IsOrd (fst κ)) where

  open SiteBound κ

  κ-in-site-bound : ⟨ fst κ ∈ˢ Lset β ⟩
  κ-in-site-bound =
    Lset-mono {α = β} {β = stage (fst κ) (snd κ)}
      (stageBound (fst κ) (snd κ) .snd .snd .snd)
      (stage-mem (fst κ) (snd κ))

  δκ : Mem (Lset β)
  δκ = fst κ , κ-in-site-bound

-- =====================================================================
-- THE OBLIGATION.  δ := κ is a member of Lset β.  The identity graph
-- is not: the tree delivers no comparison that puts a carved graph
-- under the site bound.  Hole by D-10.  InclGraph is not applied.
-- =====================================================================

module Obligation (κ : S) (oκ : IsOrd (fst κ)) where

  open SiteBound κ
  open KappaInSite κ oκ

  internal-nonempty :
    ∥ Σ[ δ ∈ Mem (Lset β) ]
        ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) κ (up δ) ∥₁ ∥₁
  internal-nonempty = ∣ δκ , graph-code ∣₁
    where
    graph-code :
      ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) κ (up δκ) ∥₁
    graph-code = {!!}
