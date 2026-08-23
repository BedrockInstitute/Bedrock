{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.565] CONTROL m.  THE SUCCESSOR STEP, WITH THE SEQUENCE NAMED
-- BY A LOCAL ABBREVIATION INSTEAD OF BY [LJ-1.536]'S IMPORTED `seq`.
--
-- Control k passed the sequence to `AdjoinAt` UNABBREVIATED and hit
-- the wall; controls d, e and g passed [LJ-1.536]'s `seq` and hit it
-- too.  Controls f, i and j show that the same shapes cost 1.71 s when
-- no such step is asked for.  This file keeps the engine imported and
-- gives the sequence a LOCAL name of exactly the shape [LJ-1.536] gave
-- it, which is the one variant not yet measured.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-565.runs.Control565q {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-inl; ∈sucV-elim )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; IsOrd; Lset )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Hierarchy {ℓ} lem using ( hierL; hierL-spec; IsHier )
open import LJ-1-536.Probe536 {ℓ} lem
  using ( step; isL-ord; HierBelow; pr-at; module AdjoinAt )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ


-- [LJ-1.565] CONTROL q.  `out` ALONE.  Control p shows the engine
-- takes `out` and `into` as hypotheses for 1.79 s; control m walls
-- when they are BUILT.  This file builds only `out`.

K : (α : V ℓ) → IsOrd α → S
K α oα = hierL (sucV α) (isL-ord (sucV α) (suc-ord oα)) (suc-ord oα)

K-spec : (α : V ℓ) (oα : IsOrd α) → IsHier (sucV α) (K α oα)
K-spec α oα = hierL-spec (sucV α) (isL-ord (sucV α) (suc-ord oα))
                (suc-ord oα)

H : (α : V ℓ) → IsOrd α → S
H α oα = hierL α (isL-ord α oα) oα

H-spec : (α : V ℓ) (oα : IsOrd α) → IsHier α (H α oα)
H-spec α oα = hierL-spec α (isL-ord α oα) oα

out : (α : V ℓ) (oα : IsOrd α) (x : S)
    → (⟨ fst x ∈ fst (H α oα) ⟩ ⊎ (fst x ≡ pr α (Lset α)))
    → ⟨ fst x ∈ fst (K α oα) ⟩
out α oα x (inl x∈H) = subst ⟨_⟩ (sym (K-spec α oα x))
  (PT.map (λ { (c , (c∈α , eq)) →
               c , (∈sucV-inl {A = α} {x = fst c} c∈α , eq) })
    (subst ⟨_⟩ (H-spec α oα x) x∈H))
out α oα x (inr p) = subst ⟨_⟩ (sym (K-spec α oα x))
  ∣ (α , isL-ord α oα) , (self∈sucV α , p) ∣₁
