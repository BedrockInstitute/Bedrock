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

module LJ-1-565.runs.Control565p {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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


-- [LJ-1.565] CONTROL p.  THE ENGINE APPLIED AT THE REAL SITE, with
-- `out` and `into` taken as HYPOTHESES instead of built.  Control o
-- shows the engine re-ascribes for 1.71 s; this row adds the site's
-- own stage, its two constants and `pr-at`, and nothing else.

K : (α : V ℓ) → IsOrd α → S
K α oα = hierL (sucV α) (isL-ord (sucV α) (suc-ord oα)) (suc-ord oα)

H : (α : V ℓ) → IsOrd α → S
H α oα = hierL α (isL-ord α oα) oα

hier∈ : (α : V ℓ) (oα : IsOrd α) (hyp : HierBelow α oα)
        (out : (x : S) → (⟨ fst x ∈ fst (H α oα) ⟩
                        ⊎ (fst x ≡ pr α (Lset α)))
             → ⟨ fst x ∈ fst (K α oα) ⟩)
        (into : (x : S) → ⟨ fst x ∈ fst (K α oα) ⟩
              → ∥ ⟨ fst x ∈ fst (H α oα) ⟩ ⊎ (fst x ≡ pr α (Lset α)) ∥₁)
      → ⟨ fst (K α oα) ∈ Lset (step 4 α) ⟩
hier∈ α oα hyp out into =
  AdjoinAt.adjoin∈ (step 3 α) (suc-ord (suc-ord (suc-ord oα)))
    (fst (H α oα)) (pr α (Lset α)) hyp (pr-at α oα) (K α oα) out into
