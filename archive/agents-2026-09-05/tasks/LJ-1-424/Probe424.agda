{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.424] PROBE.  A truncated coded graph, read as an ambient
-- arrow as DATA.  It runs in agents/tasks/LJ-1-424/ and lands nothing
-- in src/.
--
--   W3 FIRST  `good-four-selects`.  Four-conjunct Good at
--             hProp (ℓ-suc ℓ), then leastOf (orderAt β oβ) lem.
--             Typechecked ALONE, read-off omitted, result discarded.
--
--   TERM      `coded-to-arrow`.  readL applied to the four conjuncts
--             the selection returned.  Not written until W3 is green.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.
-- No ambient injection in the telescope, truncated or otherwise.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-424.Probe424 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset )
open import L.Choice.Step {ℓ} lem using ( Mem; orderAt )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( IsLeast; leastOf )
open import L.Coding.Model {ℓ} using ( svAt; domAt )
open import L.Coding.Injection {ℓ} lem using ( injAt )
open import L.Cardinal {ℓ} lem
  using ( _↪_; InjCode; module SiteBound )
open import L.CantorBernstein {ℓ} lem using ( readL )

open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- The range clause of InjCode (src/L/Cardinal.lagda.md:228), and the
-- isProp witness the brief demands rather than an assertion.
-- Reconstruction of [LJ-1.401] Probe401.agda:39-53, which returned GO.
-- =====================================================================

clause4 : S → S → Type (ℓ-suc ℓ)
clause4 F b =
  (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ fst y ∈ fst b ⟩

clause4-isProp : (F b : S) → isProp (clause4 F b)
clause4-isProp F b =
  isPropΠ (λ x → isPropΠ (λ y → isPropΠ (λ _ → snd (fst y ∈ fst b))))

isPropInjCode : (F a b : S) → isProp (InjCode F a b)
isPropInjCode F a b =
  isProp× (snd ((F ∷ a ∷ []) ⊨ svAt zero))
    (isProp× (snd ((F ∷ a ∷ []) ⊨ domAt zero (suc zero)))
      (isProp× (snd ((F ∷ a ∷ []) ⊨ injAt zero))
        (clause4-isProp F b)))

-- =====================================================================
-- W3.  Four-conjunct Good, then leastOf, result discarded.
-- Generic in a and in b.  SiteBound a in scope.
-- Typechecked alone before coded-to-arrow.
-- =====================================================================

module _ (a b : S) where

  open SiteBound a

  Good4 : Mem (Lset β) → hProp (ℓ-suc ℓ)
  Good4 A = InjCode (up A) a b , isPropInjCode (up A) a b

  good-four-selects :
      ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) a b ∥₁
    → Σ[ F ∈ Mem (Lset β) ] IsLeast (orderAt β oβ) Good4 F
  good-four-selects h = leastOf (orderAt β oβ) lem Good4 h

  -- Step two.  readL's result is definitionally _↪_ at
  -- src/L/Cardinal.lagda.md:47-48.  No repackaging.
  coded-to-arrow :
      ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) a b ∥₁
    → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫
  coded-to-arrow h = readL a b (up (fst chosen) , fst (snd chosen))
    where
    chosen = good-four-selects h
