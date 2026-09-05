{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.765] VENDORED INTERFACE, THE HULL HALF.  This file is
-- LJ-1-728-SPLIT-SPLIT-SPLIT/runs/HullHalf728SSS.agda transcribed
-- into this worktree, with the module renamed to this task's
-- namespace, the Frame import retargeted to
-- LJ-1-765.runs.Frame765, and this header rewritten.  Every other
-- line is byte-identical to the original
-- (runs/vendor-hullhalf.diff).  hullClosed, the half [LJ-1.718]
-- measured green, is the SSS transcription byte for byte.
--
--   MEASURED       green at -M4g in the SSS worktree
--                  (SSS runs/hull-2.out 243.77 s RSS 1.75 GB,
--                  runs/hull-3.out 235.43 s; re-measured here at
--                  this dispatch).
--   NO HOLE, NO POSTULATE.  One Agda process per run, caliber from
-- the pane, never set here.  Lands nothing in src/.

--                  neutral applications).
--   MEASURED       green at -M4g (runs/hull-2.out, 243.77 s, RSS 1.75 GB).
--   NO HOLE, NO POSTULATE.  One Agda process per run, caliber from
-- the pane, never set here.  Lands nothing in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-765.runs.HullHalf765 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
open import FOL.ZFStructure using ( module hPropStructure )
open hPropStructure 𝒮ᵥ

open import LJ-1-652.Probe652 {ℓ} lem as P652

open import Cubical.Data.Sigma using ( _×_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

-- plain import: Frame728SSS's inner module Build must NOT enter
-- short scope beside this file's own module Build (measured:
-- ShadowedModule, runs/hull-1.out).
import LJ-1-765.runs.Frame765 {ℓ} lem as Frame

module Build (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (elem : P652.Frame652.A.Elementary lam ordλ succλ X X⊆Lλ ∅∈λ) where

  open Frame.Build lam ordλ succλ X X⊆Lλ ∅∈λ elem

  -- Completeness to hull-closed: the half [LJ-1.718] measured green.
  hullClosed : (comp : Completeness) (δ : S) (ordδ : IsOrd δ)
             → (ca cp : Code)
             → fst (val ca) ≡ Lset δ → fst (val cp) ≡ δ
             → ∥ Σ[ a ∈ F.HS.ASt.SL ] (HullM a × SatIn a ca cp) ∥₁
  hullClosed comp δ ordδ ca cp ca≡Lδ cp≡δ =
    hull-closed (A.inBound ca cp)
      (comp ca cp (subst IsOrd (sym cp≡δ) ordδ)
                   (ca≡Lδ ∙ cong Lset (sym cp≡δ)))
