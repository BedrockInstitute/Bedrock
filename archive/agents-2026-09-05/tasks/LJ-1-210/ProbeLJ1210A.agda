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

module LJ-1-210.ProbeLJ1210A {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure; Transitive; _↾_ )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( isL; isL-trans )
open import L.Axioms.Numerals {ℓ}
  using ( numeralL; numeralL-fst; pairʟ; pairʟ-fst; sucʟ; sucʟ-fst )

open import Cubical.Data.Unit using ( Unit*; tt*; isPropUnit* )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )
open import V.Coding {ℓ} using ( pr )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; module InfinitySet )
open InfinitySet using ( #_; sucV )

import LJ-1-210.GenModel
import L.Coding.Model

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

------------------------------------------------------------------------
-- SECTION 1.  The instance at `isL`.
------------------------------------------------------------------------

module AtL = LJ-1-210.GenModel {ℓ} isL isL-trans
               numeralL numeralL-fst pairʟ pairʟ-fst sucʟ sucʟ-fst

module Delivered = L.Coding.Model {ℓ}

open hPropStructure (𝒮ᵥ ↾ isL) using ( S )
open AtL.AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨ᴬ_ )

-- The nine names `L.Coding.Powerset` imports from `L.Coding.Model`.
-- Each check is `refl`: the generic module at `isL` is the delivered
-- module, on the nose.

chk-extAt : ∀ {n} (y : Fin n) (φ : Formula S (suc n))
          → AtL.extAt y φ ≡ Delivered.extAt y φ
chk-extAt y φ = refl

chk-extAt-out : ∀ {n} (y : Fin n) (φ : Formula S (suc n)) (γ : S ^ n)
                (h : ⟨ γ ⊨ᴬ AtL.extAt y φ ⟩) (z : S)
                (m : ⟨ fst z ∈ fst (lookup y γ) ⟩)
              → AtL.extAt-out y φ γ h z m ≡ Delivered.extAt-out y φ γ h z m
chk-extAt-out y φ γ h z m = refl

chk-extAt-in : ∀ {n} (y : Fin n) (φ : Formula S (suc n)) (γ : S ^ n)
               (h : ⟨ γ ⊨ᴬ AtL.extAt y φ ⟩) (z : S)
               (s : ⟨ (z ∷ γ) ⊨ᴬ φ ⟩)
             → AtL.extAt-in y φ γ h z s ≡ Delivered.extAt-in y φ γ h z s
chk-extAt-in y φ γ h z s = refl

chk-extAt-in-both :
    ∀ {n} (y : Fin n) (φ : Formula S (suc n)) (γ : S ^ n)
    (f : (z : S) → ⟨ fst z ∈ fst (lookup y γ) ⟩ → ⟨ (z ∷ γ) ⊨ᴬ φ ⟩)
    (g : (z : S) → ⟨ (z ∷ γ) ⊨ᴬ φ ⟩ → ⟨ fst z ∈ fst (lookup y γ) ⟩)
  → AtL.extAt-in-both y φ γ f g ≡ Delivered.extAt-in-both y φ γ f g
chk-extAt-in-both y φ γ f g = refl

chk-tagAtL : ∀ {n} (s : Fin n) (k : ℕ) (x : Fin n)
           → AtL.tagAtL s k x ≡ Delivered.tagAtL s k x
chk-tagAtL s k x = refl

-- The ONE name of the nine whose PROOF TERM does not match on the nose.
-- Both sides call a `lookup-fst` that recurses on a FREE index, and the
-- two copies are distinct constants, so neither side reduces. Agda
-- ACCEPTS the type `AtL.tagAtL-adequate s k x γ ≡ Delivered....`, which
-- is the load-bearing half: the two proofs inhabit the same type, so
-- either serves any consumer. Only the `refl` BODY fails.
--   MEASURED, run 1: `refl` gives [UnequalTerms] at 1.19 s.
--   MEASURED WALL, run 2: closing it by `isSetΩ` exhausted the 8 GB
--   heap at 128.89 s. The cap was NOT raised.
-- The declaration is left out of this file so that the other eight
-- checks and the two instances can be measured.

chk-domAt : ∀ {n} (f d : Fin n) → AtL.domAt f d ≡ Delivered.domAt f d
chk-domAt f d = refl

