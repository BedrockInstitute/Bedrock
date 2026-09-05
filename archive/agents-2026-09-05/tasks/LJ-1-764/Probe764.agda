{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.764] PROBE.  conv0, the un-ascribed hull convert, exported at
-- top level.  Transcribed from VendorB4.agda.txt (the worktree's
-- Bisect4SSS.agda, module LJ-1-728-SPLIT-SPLIT-SPLIT.runs): same
-- imports, same Build scaffolding, module renamed to this task's
-- namespace, ONE export added at column 0.  B4 measured green inside
-- Build, no ascription, 12.51 s at RSS 1.93 GB, pane caliber
-- (VendorB4.agda.txt:10); the un-measured half is the top-level
-- export, and that delta is what W3 prices.
--
-- NO ascription: conv0 is the opened Spend term, its type inferred.
-- The spelled record ⟨ _ ∷ _ ∷ _ ∷ [] P652.⊨ₚ P667.matrix₃ ⟩ appears
-- NOWHERE in this file.  No hypothesis of type Convert is written.  No
-- grounded-from-complete.  Lands nothing in src/.
--
-- ONE Agda process per run, caliber from the pane, never set here.
-- Floor first: runs/Floor764.agda.txt is this file with the body a
-- hole.  Nothing is postulated.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-764.Probe764 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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

  -- B4, the constructed term, whole, NO ascription.
  conv0 = hull-convert-at-matrix

-- THE EXPORT: the same term lifted to the file's top level, its type
-- still inferred, nothing spelled.
conv0 = Build.conv0
