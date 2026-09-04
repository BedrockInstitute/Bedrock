{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1-728-SPLIT-SPLIT-SPLIT] PROBE, BISECT B6.  B2 (single clone,
-- direct Spend, the term ascribed at the inline spelling of its own
-- type) heap-walled (runs/bisect-2.out); B4 (the same term with NO
-- ascription) was green in 12.51 s (runs/bisect-4.out).  The wall is
-- in the comparison.  This file tests the DOMAIN half alone: the
-- domain is spelled, the codomain is an underscore the elaborator
-- solves from the term.  Green would mean the domain comparison is
-- innocent and the codomain half is the wall.
--
-- MEASURED: green at -M4g (runs/bisect-6.out, 140.69 s, RSS 1.85 GB).
-- NO HOLE: the underscore is a SOLVED meta, not an open goal.  One
-- Agda process per run, caliber from the pane, never set here.
-- Lands nothing in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-728-SPLIT-SPLIT-SPLIT.runs.Bisect6SSS {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
open import FOL.ZFStructure using ( module hPropStructure )
open hPropStructure 𝒮ᵥ
open import FOL.Manipulation.Relabelling using ( mapFo )

open import LJ-1-652.Probe652 {ℓ} lem as P652
open import LJ-1-673.Probe673 {ℓ} lem as P673
import LJ-1-692.Probe692 {ℓ} lem as P692

module Build (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (elem : P652.Frame652.A.Elementary lam ordλ succλ X X⊆Lλ ∅∈λ) where

  module A = P673.At lam ordλ succλ X X⊆Lλ ∅∈λ elem
  module F = A.F
  module HS = F.HS

  open F.HS.H.T using ( Code; val )

  open P692.Spend lam ordλ succλ X X⊆Lλ ∅∈λ elem
    using ( hull-convert-at-matrix )

  -- B6: domain spelled, codomain solved.
  conv0 : (ca cp : Code) (a : F.HS.ASt.SL)
        → ⟨ (a ∷ []) F.HS.ASt.AbsL.⊨ᵐ (mapFo val (A.inBound ca cp)) ⟩
        → _
  conv0 = hull-convert-at-matrix
