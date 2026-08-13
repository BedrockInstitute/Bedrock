{-# OPTIONS --cubical --safe --guardedness #-}

-- [DD25 review of LJ-1.33] FLOOR: the import cone of the layer probes,
-- with no content at all.  Its cold seconds are the floor that every
-- figure in this review sits on top of.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeDD25CF {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∃̇_; ∀̇_; ∃̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; 𝒟ₒ )
open import L.Coding.Model {ℓ}
  using ( appAt; appAt-adequate; extAt; extAt-out; extAt-in; extAt-in-both )
open import L.Coding.Powerset {ℓ} lem
  using ( DefAt; DefAt-in; DefAt-out; DefOK )
open import L.Coding.Sequence {ℓ} lem
  using ( StepAt; StepBody; Records; StepOf; PowOK )
open import L.Condensation {ℓ} lem
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
