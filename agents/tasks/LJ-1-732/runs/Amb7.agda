{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-732.runs.Amb7 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import Cubical.Data.Vec using ( lookup )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open import LJ-1-652.Probe652 {ℓ} lem as P652
import LJ-1-520.Probe520 {ℓ} lem as P520
open import V.Model {ℓ} using ( empty-spec )
open import LJ-1-732.runs.Num {ℓ} lem
open import LJ-1-732.runs.Amb1 {ℓ} lem

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

open import LJ-1-732.runs.Amb5 {ℓ} lem
open import LJ-1-732.runs.Amb7a {ℓ} lem

-- the approximation half of the graph at the empty table: the domain
-- row from Amb5, and the step row killed at its own appAt binder
-- over the empty table.  The reading and the motive are Amb7a's
-- named types, so each normal form is built once and shared.
approx-part : ApproxAt
approx-part = domB-part , (λ u u∈ v v∈ ant →
    PT.rec
      (MotiveEmpty u v .snd)
      (λ { (pr , pr∈∅ , _) →
            Empty.rec* (subst ⟨_⟩ (empty-spec pr) pr∈∅) })
      ant)
