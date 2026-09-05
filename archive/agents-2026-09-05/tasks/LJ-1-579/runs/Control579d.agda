{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.579] CONTROL d.  THE OTHER HALF OF THE LIMIT CASE.
-- At a LIMIT γ the table `hierL γ` is a SUBSET of `Lset γ`.  So the
-- limit case needs no bound at all: it needs DEFINABILITY over a stage
-- the set already sits inside.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-579.runs.Control579d {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Hierarchy {ℓ} lem using ( hierL; hierL-spec; Recorded )
open import LJ-1-536.Probe536 {ℓ} lem using ( step; pr-at; IsLimit )

import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

------------------------------------------------------------------------
-- AT A LIMIT, THE TABLE LIES INSIDE THE STAGE.
--
-- Every member of `hierL γ` is `pr c (Lset c)` for some c ∈ γ
-- (src/L/Hierarchy.lagda.md:497-502), that pair lies in
-- `Lset (step 3 c)` (agents/tasks/LJ-1-536/Probe536.agda:163-164), and
-- a limit is closed under the successor, three times over.
------------------------------------------------------------------------

hier-sub : (γ : V ℓ) (h : ⟨ isL γ ⟩) (o : IsOrd γ) → IsLimit γ
         → (z : V ℓ) → ⟨ z ∈ fst (hierL γ h o) ⟩ → ⟨ z ∈ Lset γ ⟩
hier-sub γ h o lim z z∈ = PT.rec (snd (z ∈ Lset γ)) use rec
  where
  zS : S
  zS = z , isL-trans {x = fst (hierL γ h o)} {y = z} z∈ (snd (hierL γ h o))

  rec : ⟨ Recorded γ z ⟩
  rec = subst ⟨_⟩ (hierL-spec γ h o zS) z∈

  use : Σ[ c ∈ S ] (⟨ fst c ∈ γ ⟩ × (z ≡ pr (fst c) (Lset (fst c))))
      → ⟨ z ∈ Lset γ ⟩
  use (c , (c∈γ , eq)) =
    subst (λ w → ⟨ w ∈ Lset γ ⟩) (sym eq)
      (Lset-mono step3∈γ (pr-at (fst c) oc))
    where
    oc : IsOrd (fst c)
    oc = mem-ord {A = γ} o (fst c) c∈γ
    step3∈γ : ⟨ step 3 (fst c) ∈ γ ⟩
    step3∈γ = lim _ (lim _ (lim _ c∈γ))
