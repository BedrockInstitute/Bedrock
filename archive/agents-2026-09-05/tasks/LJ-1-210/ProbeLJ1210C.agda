{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.210] the TWO instantiations of the class-generic
-- `L.Coding.Model`.
--
--   SECTION 1  the instance at `isL`, and nine `refl` checks that it
--              IS the delivered module
--   SECTION 2  the instance at the AMBIENT class `Full`
--
-- DD4.  The generic module is `agents/tasks/LJ-1-210/GenModel.agda`.
-- Nothing in its 1,288 body lines names `isL`, `𝒮ʟ` or a tower stage.
-- The class is a module parameter with one transitivity hypothesis and
-- six numeral operations.  Both instances below apply the same module.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".  Tracked, never
-- deleted, and it lives beside its report.

open import Base.Prelude
open import Base.Truth

module LJ-1-210.ProbeLJ1210C {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure; Transitive; _↾_ )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )




open import Cubical.Data.Unit using ( Unit*; tt*; isPropUnit* )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )
open import V.Coding {ℓ} using ( pr )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; module InfinitySet )
open InfinitySet using ( #_; sucV )

import LJ-1-210.GenModel


open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

------------------------------------------------------------------------
-- SECTION 2.  The instance at the AMBIENT class `Full`.
------------------------------------------------------------------------

Full : V ℓ → hProp (ℓ-suc ℓ)
Full _ = Unit* , isPropUnit*

Full-trans : Transitive 𝒮ᵥ Full
Full-trans {x} {y} _ _ = tt*

numeralF : ℕ → Σ[ x ∈ V ℓ ] ⟨ Full x ⟩
numeralF k = # k , tt*

numeralF-fst : (k : ℕ) → fst (numeralF k) ≡ # k
numeralF-fst k = refl

pairF : (a b : Σ[ x ∈ V ℓ ] ⟨ Full x ⟩) → Σ[ x ∈ V ℓ ] ⟨ Full x ⟩
pairF a b = ⁅ fst a , fst b ⁆ , tt*

pairF-fst : (a b : Σ[ x ∈ V ℓ ] ⟨ Full x ⟩)
          → fst (pairF a b) ≡ ⁅ fst a , fst b ⁆
pairF-fst a b = refl

sucF : Σ[ x ∈ V ℓ ] ⟨ Full x ⟩ → Σ[ x ∈ V ℓ ] ⟨ Full x ⟩
sucF a = sucV (fst a) , tt*

sucF-fst : (a : Σ[ x ∈ V ℓ ] ⟨ Full x ⟩) → fst (sucF a) ≡ sucV (fst a)
sucF-fst a = refl

module AtFull = LJ-1-210.GenModel {ℓ} Full (λ {x} {y} → Full-trans {x} {y})
                  numeralF numeralF-fst pairF pairF-fst sucF sucF-fst
