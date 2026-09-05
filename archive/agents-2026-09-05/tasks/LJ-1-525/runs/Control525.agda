{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.525] CONTROL.  The same import list as Probe525.agda and NO
-- term of its own.  It separates the chapter-load price from the price
-- of the leaf conversion itself: `L.Condensation` is a large chapter
-- and its interface load is most of the probe's wall time.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-525.runs.Control525 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; ∃̇_; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset )
open import L.Coding.Model {ℓ} using ( extAt )
open import L.Coding.Powerset {ℓ} lem using ( DefBody; DefAt )
open import L.Condensation {ℓ} lem
  using ( extAtB; extAtB→extAt; module StepB; module StepAtB )

open import LJ-1-522.Probe522 {ℓ} lem using ( IsLimit; defPow-closed-noCode )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( lookup; _∷_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
