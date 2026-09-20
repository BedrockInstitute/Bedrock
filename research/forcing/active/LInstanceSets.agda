{-# OPTIONS --cubical --safe --guardedness #-}

-- K3 Track J, file 2 of 7. Tier 2 of the ground ledger at 𝒮ʟ, and the PowerSet
-- operation, which is not a tier but which two K3 modules take as an argument
-- (NameSpace.nameBound, NameWeight.Over).
--
-- This is the first file of the track that takes the excluded middle. It takes
-- exactly the one hypothesis L⊨ZFC already takes, LEM (ℓ-suc ℓ), and it takes
-- it for one reason: Separation at L is proved by reflecting an arbitrary
-- formula at a stage that contains the argument (L/Axioms/Full.lagda.md:173),
-- and the reflection principle is where the classical step lives. Pairing,
-- union, extensionality and accessibility did not need it, which is why they
-- are in file 1 and not here. K3 adds no level and no second hypothesis to the
-- T3 budget.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LInstanceSets {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Axioms.Power {ℓ} lem using ( hasPowerL )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

import NameKernel
import OrdinaryProfile
open import LInstanceCore {ℓ} using ( coreL; unionL )

module NK = NameKernel 𝒮ʟ
module OP = OrdinaryProfile 𝒮ʟ

open OP using ( Separation; PowerSet; spec-to-iff )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ)) hiding ( ¬_ )
open hPropStructure 𝒮ʟ

-- ---------------------------------------------------------------------
-- Separation
-- ---------------------------------------------------------------------

-- The same two moves as pairing and union in file 1: project the centre of
-- the contraction, convert its pointwise path specification into the internal
-- biconditional. What is worth a sentence is that the two satisfaction
-- relations involved are the SAME relation and not two that happen to agree.
-- L.Axioms.Full reads its formulas through FOL.Absoluteness.Single's ⊨ᵐ,
-- which is by definition satisfaction in 𝒮ᵥ ↾ isL (FOL/Absoluteness.lagda.md:85-97),
-- and 𝒮ʟ IS 𝒮ᵥ ↾ isL. So the ordinary profile's ⊨ at 𝒮ʟ and Full's ⊨ are one
-- term, and no transport is needed at this crossing. Had they been merely
-- equivalent, every formula in K3 would have needed a bridge lemma here.

separationL : Separation
separationL a φ = ∣ s , spec-to-iff s _ sp ∣₁
  where
  s  = hasSeparationL a φ .fst .fst
  sp = hasSeparationL a φ .fst .snd

-- ---------------------------------------------------------------------
-- PowerSet, which is not a tier
-- ---------------------------------------------------------------------

-- Section 1.6 keeps PowerSet out of NameGround.Families deliberately and
-- passes it as an argument to the two declarations that use it, so that a
-- ground without power sets still supports the whole of the name apparatus
-- except the bound. The L instance supplies it, and the shape of that supply
-- is the ordinary profile's operation and not a tier record.

powerL : PowerSet
powerL a = ∣ v , spec-to-iff v _ sp ∣₁
  where
  v  = hasPowerL a .fst .fst
  sp = hasPowerL a .fst .snd

-- ---------------------------------------------------------------------
-- The tier 2 record, sealed
-- ---------------------------------------------------------------------

-- Sealed for the reason given in file 1. Note what is inside the seal: a
-- field whose value is itself a sealed record from another file. Opacity
-- composes, so a consumer of setsL that projects `core` receives coreL as a
-- neutral constant and not as the L model.

opaque
  setsL : NK.Sets
  setsL = record
    { core          = coreL
    ; hasUnion      = unionL
    ; hasSeparation = separationL }
