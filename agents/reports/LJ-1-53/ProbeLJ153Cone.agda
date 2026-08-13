{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.53] the import cone of ProbeLJ153A: the same imports, no
-- content.  The difference from ProbeLJ153A is the marginal rate of the
-- wall-2 content.  Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ153Cone {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( ZFStructure; module hPropStructure; _↾_ )
open import FOL.Syntax using
  ( Term; con; var; Formula
  ; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import FOL.Semantics
open import FOL.Manipulation.Renaming using ( renameTm )
open import FOL.Manipulation.Relabelling using ( mapTm; mapFo; mapFo-comp )
open import FOL.Manipulation.Parameters using ( lookup-map )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO; leastOf; IsLeast )
open import V.Presentation {ℓ} using ( member )
open import Cubical.Functions.Embedding using ( Embedding-into-isSet→isSet )
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( isL; isL-trans; IsOrd; Lset )
open import L.Hull {ℓ} lem using ( module AtStage )

open hPropStructure 𝒮ᵥ

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.Data.Vec using ( Vec; lookup; map; _∷_; []; _++_ )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Foundations.Prelude using ( funExt; transport )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ∅ )

trivial : Type (ℓ-suc ℓ)
trivial = S
