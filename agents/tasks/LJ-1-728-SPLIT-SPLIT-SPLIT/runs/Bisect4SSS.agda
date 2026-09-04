{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1-728-SPLIT-SPLIT-SPLIT] PROBE, BISECT B4.  B1 (double clone)
-- and B2 (single clone) both wall on the same comparison: a spelled
-- PI against the Spend-opened term's type.  This file ascribes
-- NOTHING: conv0 is the opened term, its type inferred, no
-- comparison forced.  Green would mean the cloned type is readable
-- and the wall sits in the comparison itself.
--
-- MEASURED: green at -M4g (runs/bisect-4.out, 12.51 s, RSS 1.93 GB).
-- NO HOLE, NO POSTULATE.  One Agda process per run, caliber from the
-- pane, never set here.  Lands nothing in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-728-SPLIT-SPLIT-SPLIT.runs.Bisect4SSS {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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
