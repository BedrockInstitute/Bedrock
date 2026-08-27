{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.692] PROBE.  Spend [LJ-1.689]'s hull-convert at matrix₃.
-- Instantiation, not a rewrite.  Lands nothing in src/.
--
--   W3              whether the instantiation elaborates at
--                   matrix₃'s own slide and val
--                   (agents/tasks/LJ-1-689/lj-1.689-report.md:345-351).
--   THE OBLIGATION  hull-convert-at-matrix.  hull-convert at
--                   {φ = matrix₃} with Δ₀-matrix₃, Probe673.slide
--                   and Probe673.val, leftover equation discharged
--                   by Probe686.slide-embed-eq.  The result is
--                   At.Convert (Probe673.agda:115-119).
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing is postulated.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-692.Probe692 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
open import FOL.ZFStructure using ( module hPropStructure )
open hPropStructure 𝒮ᵥ

open import LJ-1-652.Probe652 {ℓ} lem as P652
open import LJ-1-667.Probe667 {ℓ} lem as P667
open import LJ-1-673.Probe673 {ℓ} lem as P673
open import LJ-1-686.Probe686 {ℓ} lem as P686
import LJ-1-689.Probe689 {ℓ} as P689

open P667 using ( matrix₃; Δ₀-matrix₃ )

-- W2: hull-convert is the generic transport.  This is the instance
-- at the delivered matrix and the hull maps.  The leftover equation
-- is applied, not re-inhabited.  convert-generic, pin₃, pin₃-map
-- and convert-at-matrix are not rewritten.

module Spend (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (elem : P652.Frame652.A.Elementary lam ordλ succλ X X⊆Lλ ∅∈λ) where

  module A = P673.At lam ordλ succλ X X⊆Lλ ∅∈λ elem
  module F = P652.Frame652 lam ordλ succλ X X⊆Lλ ∅∈λ
  open A using (slide; Convert)
  -- val is opened inside At (Probe673.agda:69) and is not
  -- re-exported.  This is that same name.
  open A.F.HS.H.T using (val)
  open P689.Convert (Lset lam) F.HS.ASt.Ltr

  -- THE OBLIGATION.  Fully discharged Convert at the site clause
  -- (iii) needs.  Lifted off this module so the witness meter reads
  -- Target.hull-convert-at-matrix (scripts/pod/witness.py:278).
  hull-convert-at-matrix : Convert
  hull-convert-at-matrix =
    hull-convert {φ = matrix₃} Δ₀-matrix₃ slide val
      (P686.slide-embed-eq slide val)

hull-convert-at-matrix = Spend.hull-convert-at-matrix
