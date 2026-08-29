{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-732.runs.Amb3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; ⊥̇; ∃̇∈; ∀̇∈ )
open import FOL.Manipulation.Parameters using ( countFo )
import FOL.Count
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; Lset )
open import L.Condensation {ℓ} lem using ( domB )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Vec using ( lookup; _∷_; [] )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅ )
open import LJ-1-652.Probe652 {ℓ} lem as P652
open import LJ-1-667.Probe667 {ℓ} lem as P667
import LJ-1-520.Probe520 {ℓ} lem as P520
open import V.Model {ℓ} using ( empty-spec )
open import LJ-1-732.runs.Num {ℓ} lem
open import LJ-1-732.runs.Amb1 {ℓ} lem

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- the transitive-bound row and the twelve pin slots of the erased
-- matrix at the empty instance
transK-part : ⟨ γ15 P652.⊨ₚ CntS.erase Mx.transK countTrans ⟩
transK-part = λ u u∈ v v∈u → trZ v∈u u∈

pins-part : ⟨ γ15 P652.⊨ₚ CntS.erase Mx.pins countPins ⟩
pins-part =
    (λ x h → Empty.rec* (subst ⟨_⟩ (empty-spec x) h))
  , ( sucPin (n 0)
    , ( sucPin (n 1)
    , ( sucPin (n 2)
    , ( sucPin (n 3)
    , ( sucPin (n 4)
    , ( sucPin (n 5)
    , ( sucPin (n 6)
    , ( sucPin (n 7)
    , ( sucPin (n 8)
    , ( sucPin (n 9)
    , ( sucPin (n 10) ) ) ) ) ) ) ) ) ) ) )
