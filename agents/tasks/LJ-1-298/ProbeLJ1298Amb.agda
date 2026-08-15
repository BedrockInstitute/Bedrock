{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.298] ambient probe.  DOES THE GENERIC `TagAgree` INSTANTIATE AT
-- THE AMBIENT CLASS.
--
-- `GenTagAgree.agda` re-instantiated `TagAgree` with the class as a
-- parameter.  This file applies it at the AMBIENT class `Full`, with the
-- ambient numerals, pairs and successor that `[LJ-1.297]`'s probe D
-- already supplied for `GenSequence`
-- (`agents/tasks/LJ-1-297/ProbeLJ1297D.agda:44-50`), and moves the two
-- directions to the AMBIENT READING `A.ambient` through probe C's
-- `absFull`.  Green here means: one generic port plus the ambient class
-- gives `TagAgree` at the carrier and reading `q'` lives at.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure; Transitive; _↾_ )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆ ) renaming ( module InfinitySet to Inf )
open Inf using ( #_; sucV )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.Data.Vec using ( map )

import LJ-1-298.GenTagAgree

module LJ-1-298.ProbeLJ1298Amb {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
import LJ-1-184.ProbeLJ1184A {ℓ} as P184
import LJ-1-297.ProbeLJ1297A {ℓ} lem as P1297A
import LJ-1-297.ProbeLJ1297C {ℓ} as P1297C

module A = P184.Ambient
open P1297C using ( absFull )

-- The ambient class supplies all eight parameters, in the shape probe D
-- used for `GenSequence`.
module GTA = LJ-1-298.GenTagAgree {ℓ} P1297A.Full
  (λ {x} {y} → P1297A.Full-tr {x} {y})
  (λ k → # k , tt*) (λ k → refl)
  (λ a b → ⁅ fst a , fst b ⁆ , tt*) (λ a b → refl)
  (λ a → sucV (fst a) , tt*) (λ a → refl)

-- The reading the generic module carries, at the ambient class.  The
-- same `Single` application GTA opens internally, so the two readings
-- are judgmentally the same one.
module AbsF = FOL.Absoluteness.Single 𝒮ᵥ P1297A.Full
  (λ {x} {y} → P1297A.Full-tr {x} {y})
open AbsF using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- The reading transport, probe C's, at the generic module's reading.
toAmb : ∀ {n} (φ : Formula A.R.SC n) (γ : A.R.SC ^ n)
      → ⟨ γ ⊨ φ ⟩ → ⟨ A.ambient γ φ ⟩
toAmb φ γ = subst ⟨_⟩ (absFull φ γ)

fromAmb : ∀ {n} (φ : Formula A.R.SC n) (γ : A.R.SC ^ n)
        → ⟨ A.ambient γ φ ⟩ → ⟨ γ ⊨ φ ⟩
fromAmb φ γ = subst ⟨_⟩ (sym (absFull φ γ))

-- `TagAgree` at the ambient carrier, with the hypotheses the module's
-- own telescope names.  `out-amb` and `back-amb` are the two directions
-- at the AMBIENT READING.
module Check {n : ℕ} (s tag x K : Fin n) (γ : A.R.SC ^ n) (k : ℕ)
  (tagEq : fst (lookup tag γ) ≡ # k)
  (numK : ⟨ # k ∈ fst (lookup K γ) ⟩) where

  module TA = GTA.TagAgree s tag x K γ k tagEq numK

  out-amb : ⟨ A.ambient γ (GTA.GM.tagAtL s k x) ⟩
          → ⟨ A.ambient γ (GTA.tagBS s tag x K) ⟩
  out-amb h = toAmb (GTA.tagBS s tag x K) γ
    (TA.out (fromAmb (GTA.GM.tagAtL s k x) γ h))

  back-amb : ⟨ A.ambient γ (GTA.tagBS s tag x K) ⟩
           → ⟨ A.ambient γ (GTA.GM.tagAtL s k x) ⟩
  back-amb h = toAmb (GTA.GM.tagAtL s k x) γ
    (TA.back (fromAmb (GTA.tagBS s tag x K) γ h))
