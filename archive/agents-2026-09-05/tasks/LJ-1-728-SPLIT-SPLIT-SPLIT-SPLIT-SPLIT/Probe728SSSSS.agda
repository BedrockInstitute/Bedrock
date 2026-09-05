{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1-728-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT] PROBE, conv0 AT HEAVY.
-- Transcribed from VendorB4.agda.txt (the worktree's
-- Bisect4SSS.agda): B4, the constructed term with NO ascription,
-- whose SSS run was green at -M4g (12.51 s, RSS 1.93 GB,
-- LJ-1-728-SPLIT-SPLIT-SPLIT/runs/bisect-4.out:5,23).  This file is
-- that term NAMED: the same body, plus the top-level export the
-- vendor did not carry (the Probe692.agda:68 pattern), so the
-- witness meter can read Probe728SSSSS.agda::conv0.
--
--   W3  whether the un-ascribed convert, exported at top level,
--       checks at -M4g in this task's module.  Estimate: the B4 file
--       plus one export.
--
-- The codomain is never spelled and nothing is ascribed; the wall the
-- bisection measured sits in the codomain comparison, and B8's
-- ascribed shape is not retried (four measured walls: B2, B8, conv-1,
-- amb-1).  Convert is not hypothesised and grounded-from-complete is
-- not inhabited; the split composition is a later brief.  NO HOLE, NO
-- POSTULATE.  One Agda process per run, caliber from the pane, never
-- set here.  Lands nothing in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-728-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT.Probe728SSSSS {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
open import FOL.ZFStructure using ( module hPropStructure )
open hPropStructure 𝒮ᵥ

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

  -- B4: the constructed term, whole, NO ascription.
  conv0 = hull-convert-at-matrix

-- THE OBLIGATION'S NAME, exported at the file's top level
-- (Probe692.agda:66's pattern).
conv0 = Build.conv0
