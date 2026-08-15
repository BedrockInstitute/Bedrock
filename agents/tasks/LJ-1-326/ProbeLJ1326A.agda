{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.326] PROBE.  Do the delivered four conjuncts assemble into an
-- `InjCode`, and does the assembly reach `InjL κ (𝒫 κ)`?
--
-- THE LEAD.  `[LJ-1.325]` measured that `InjCode`
-- (src/L/Cardinal.lagda.md:223-228) is a four-part product, and that
-- `L.InjChain.Carve` (src/L/InjChain.lagda.md:513-547) proves exactly
-- those four facts under the heading「THE FOUR CONJUNCTS」.  It did not
-- form the tuple.  C-45: a proof that is not exported supplies nothing.
--
-- PART 1, MINIATURE A.  The tuple at the ordinal inclusion, generic in
-- the ordinal pair.  It measures whether the four delivered facts TYPE
-- as an `InjCode`.
--
-- PART 2, THE DEBT-2 MINIATURE.  `InjL κ (𝒫 κ)`.  Every member of an
-- ordinal is a subset of it, so the power-set specification accepts it,
-- and the inclusion graph is the injection.
--
-- Nothing lands.  Tracked probe.  ONE agda process under
-- GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-326.ProbeLJ1326A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.ZFModel
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL-trans; IsOrd )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.GCH {ℓ} lem using ( InjL )
open import L.InjChain {ℓ} lem using ( module InclGraph; module OrdIncl )
open import L.Absorption {ℓ} lem using ( module ShiftGraph )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_ )
open import Cubical.Data.Nat using ( ℕ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( ℩-spec; _⊆ˢ_ )

-- ---------------------------------------------------------------------
-- PART 1.  MINIATURE A.  The tuple, at the delivered ordinal inclusion.
--
-- `OrdIncl` (src/L/InjChain.lagda.md:604-607) opens `Carve` public, so
-- `sv`, `dm`, `ij` and `ran` are reachable from outside.  This module
-- is generic in the ordinal pair, so it measures the TYPES and not one
-- delivered site.
-- ---------------------------------------------------------------------

module MiniA (C : S) (oC : IsOrd (fst C))
             (D : S) (D∈C : ⟨ fst D ∈ fst C ⟩) where

  module O = OrdIncl C oC D D∈C

  codeA : InjCode O.G D C
  codeA = O.sv , O.dm , O.ij , O.ran

  injA : InjL D C
  injA = ∣ O.G , codeA ∣₁

-- ---------------------------------------------------------------------
-- PART 1b.  MINIATURE A AT DEBT 1's OWN SITE (P-l: a measured cure does
-- not transfer by analogy).  The ruling's own named miniature was「code
-- `absorbs` at its smallest site into an `InjCode` witness」
-- (agents/tasks/LJ-1-323/lj-1.323-ruling.md:258-260).  `ShiftGraph`
-- (src/L/Absorption.lagda.md:538-605) opens `Carve` public, so the same
-- four names are reachable, at the shift pair.
-- ---------------------------------------------------------------------

module MiniShift (γ : S) (oγ : IsOrd (fst γ))
                 (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
                 (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩) where

  module SG = ShiftGraph γ oγ γ∉ω numerals

  codeS : InjCode SG.G SG.D SG.C
  codeS = SG.sv , SG.dm , SG.ij , SG.ran

  injS : InjL SG.D SG.C
  injS = ∣ SG.G , codeS ∣₁

-- ---------------------------------------------------------------------
-- PART 2.  THE DEBT-2 MINIATURE.  `InjL κ (𝒫 κ)`.
--
-- The subset witness is the ordinal's own transitivity, read through
-- the power-set specification `℩-spec (hasPower κ)`
-- (src/FOL/ZFModel.lagda.md:199 and :287-288).
-- ---------------------------------------------------------------------

module Reverse (zf : ModelL.isZFModel) (κ : S) (oκ : IsOrd (fst κ)) where

  open ModelL.isZFModel zf using ( 𝒫; hasPower )

  sub : (z : V ℓ) → ⟨ z ∈ fst κ ⟩ → ⟨ z ∈ fst (𝒫 κ) ⟩
  sub z z∈κ = subst ⟨_⟩ (sym (℩-spec (hasPower κ) zS)) zS⊆κ
    where
    zS : S
    zS = z , isL-trans z∈κ (snd κ)

    zS⊆κ : ⟨ zS ⊆ˢ κ ⟩
    zS⊆κ x x∈z = oκ .fst x∈z z∈κ

  module I = InclGraph κ (𝒫 κ) sub

  code : InjCode I.G κ (𝒫 κ)
  code = I.sv , I.dm , I.ij , I.ran

  injκ : InjL κ (𝒫 κ)
  injκ = ∣ I.G , code ∣₁
