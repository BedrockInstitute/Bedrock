{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.340 probe C.  It lands nothing.  It runs in agents/tasks/LJ-1-340/.
--
-- TWO QUESTIONS ProbeGeneric.agda leaves open.
--
-- PART A: the LANDING SHAPE.  ProbeGeneric.agda drops `meet-suc`, which
--         `[LJ-1.339]:39` measured has no consumer outside its chapter.
--         Dropping a delivered export is a retirement and DD13 prices it
--         separately.  PART A keeps EVERY delivered export and re-prices.
--
-- PART B: is the generic form GENERIC, or a two-point curve fit?  A third
--         instance answers that.  `src/L/Reflect.lagda.md:175` takes the
--         least stage holding a witness of a formula, through the SAME
--         `leastOrd` operator.  Its property has Stage's shape: a truncated
--         existential over a member of `Lset σ`.  If the generic form is
--         real, that third site costs an application and nothing else.
--         NOTHING IN `src/` DEMANDS PART B TODAY.  It is a genericity test.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-340.ProbeThird {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; isL; isL-trans; Lset )
import FOL.Absoluteness
open import L.Stage {ℓ} lem using ( isLeastOrd; LeastOrd )
open import L.Reflect {ℓ} lem using ( Sat; SatEx; Wit; pick )
open import L.Choice.Stage {ℓ} lem
  using ( meets; Inhabited; μ; μ-ord; μ-meets; μ-earliest; IsPredOf )
open import LJ-1-340.ProbeGeneric {ℓ} lem using ( Carved; predOf; carveAt )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
open hPropStructure 𝒮ʟ using () renaming ( S to Sʟ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ )

------------------------------------------------------------------------
-- PART A.  The landing shape: `meet-suc` KEPT, at its delivered type.
------------------------------------------------------------------------

carveMeets : (u σ : S) → ⟨ meets u σ ⟩ → ∥ Carved (meets u) σ ∥₁
carveMeets u σ = PT.rec squash₁
  (λ { (z , (z∈u , z∈Lσ)) → carveAt (meets u) σ z z∈Lσ
    (λ δ hz → ∣ z , (z∈u , hz) ∣₁) })

meet-suc : (u σ : S) → IsOrd σ → ⟨ meets u σ ⟩ → isLeastOrd (meets u) σ
         → ∥ Σ[ δ ∈ S ] IsPredOf σ δ ∥₁
meet-suc u σ ordσ m least = ∣ predOf (meets u) σ ordσ least (carveMeets u σ m) ∣₁

thePred : (u : S) (pu : ⟨ isL u ⟩) (h : Inhabited u)
        → Σ[ δ ∈ S ] IsPredOf (μ u pu h) δ
thePred u pu h = predOf (meets u) (μ u pu h) (μ-ord u pu h) (μ-earliest u pu h)
  (carveMeets u (μ u pu h) (μ-meets u pu h))

------------------------------------------------------------------------
-- PART B.  The third instance.  `src/L/Reflect.lagda.md:175`.
------------------------------------------------------------------------

carveWit : {k : ℕ} (ψ : Formula Sʟ (suc k)) (ρ : Sʟ ^ k) (σ : S)
         → ⟨ Wit ψ ρ σ ⟩ → ∥ Carved (Wit ψ ρ) σ ∥₁
carveWit ψ ρ σ = PT.rec squash₁
  (λ { (q , (q∈Lσ , satq)) → carveAt (Wit ψ ρ) σ (fst q) q∈Lσ
    (λ δ hz → ∣ q , (hz , satq) ∣₁) })

witPred : {k : ℕ} (ψ : Formula Sʟ (suc k)) (ρ : Sʟ ^ k) (sat : ⟨ SatEx ψ ρ ⟩)
        → Σ[ δ ∈ S ] IsPredOf (pick ψ ρ sat .fst) δ
witPred ψ ρ sat = predOf (Wit ψ ρ) (pick ψ ρ sat .fst)
  (pick ψ ρ sat .snd .fst) (pick ψ ρ sat .snd .snd .snd)
  (carveWit ψ ρ (pick ψ ρ sat .fst) (pick ψ ρ sat .snd .snd .fst))
