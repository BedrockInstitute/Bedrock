{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.48] THE IMPORT-CONE CONTROL.
--
-- Imports the same modules as src/ProbeLJ148.agda and checks nothing
-- else.  The probe's own content time is the probe's cold time minus
-- this cone's cold time, at the same caliber, warm dependencies.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ148Cone {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure; _↾_ )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
  ; Term; ∃̇_; ∀̇_; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∀∈; δ-∃∈
  ; Σ₁; σ-Δ₀; σ-∃ )
open import FOL.Manipulation.Relabelling using ( mapFo; mapTm; mapFo-comp; embed; mapΔ₀ )
import FOL.Absoluteness
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import L.Coding.Model {ℓ}
  using ( appAt; extAt; extAt-in-both; envSetAt )
open import L.Condensation {ℓ} lem using
  ( extAtB; Δ₀-extAtB
  ; DefBodyB; Δ₀-DefBodyB
  ; module StepAtB; module ApproxB; module GraphB
  ; existCertAt; Σ₁-cert
  ; module EraseTransfer
  ; ride-only; ride-defines
  )
open import L.Hull {ℓ} lem using ( module AtStage )
open import V.Collapse {ℓ} using ( module Collapse; isExt; isTrans )

open import Cubical.Data.Nat using ( _+_ )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.Data.Vec using ( Vec; map; lookup; _∷_; [] )
open import Cubical.Data.Sigma using ( _×_; _,_; Σ≡Prop )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; sett; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ∅ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; extensionality )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module CS = hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- the cone checks nothing but the imports
probe-cone : Type (ℓ-suc ℓ)
probe-cone = CS.S
