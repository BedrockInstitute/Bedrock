{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.609]  W3 SLICE.  TYPE ONLY, TYPECHECKED ALONE, WRITTEN FIRST.
--
-- The brief names the widest unmeasured term: "the six missing slots,
-- listed by name with their arities, TYPE ONLY".  The six are [LJ-1.606]'s
-- Frame parameters (agents/tasks/LJ-1-606/Probe606.agda:104-109), and the
-- type below is face E over exactly those six: `ElemDownAt`
-- (Probe606.agda:147-148), which is `DownReflect.ElemDown`
-- (src/L/BoundedSubset.lagda.md:410-412) at the GENERAL carrier X.
-- [LJ-1.578] delivered it only at the seventeen-slot frame, whose carrier
-- is FORCED to UK.X = Lset α ∪ ⁅ x ⁆s (src/L/BoundedSubset.lagda.md:1150;
-- agents/tasks/LJ-1-578/Probe578.agda:413-427).
--
-- No formula is chosen and no inhabitant is claimed: this slice is a TYPE.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-609.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( sucV )
import LJ-1-606.Probe606 {ℓ} lem as P606

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )

-- THE SIX, TYPE ONLY.  Each slot named, at the arity [LJ-1.606]'s Frame
-- gives it (Probe606.agda:104-109); the target is face E as that probe
-- stated it (Probe606.agda:147-148).
ElemDownAt6 : Type (ℓ-suc ℓ)
ElemDownAt6 =
    (lam : SV.S)                             -- slot 1: the limit stage
    (ordλ : IsOrd lam)                       -- slot 2: its ordinality
    (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩       -- slot 3: sucV-closure
             → ⟨ sucV d ∈ˢ lam ⟩)
    (X : SV.S)                               -- slot 4: the carrier, GENERAL
    (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩          -- slot 5: bounded in the stage
             → ⟨ z ∈ˢ Lset lam ⟩)
    (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)                     -- slot 6: nonempty base
  → P606.Frame.ElemDownAt lam ordλ succλ X X⊆Lλ ∅∈λ
