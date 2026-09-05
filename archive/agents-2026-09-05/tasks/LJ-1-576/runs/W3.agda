{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.576]  W3, THE WIDEST UNMEASURED TERM, WRITTEN FIRST AND ALONE.
--
-- The brief names it: "whether `InjCode` is an hProp at today's tree",
-- with the stub
--
--     -- isProp (InjCode F a b), at this frame, INHABITED or refuted
--
-- [LJ-1.314]'s archived cure turns on it (archive/dev/LJ-dispatch-index.md:371)
-- and that is an OLD tree.  This file re-measures it here.
--
-- It ALSO writes down, TYPE ONLY and with no inhabitant, the question
-- the ROUTE actually turns on, which is not the same question:
-- `leastOf` untruncates `∥ Σ[ F ∈ S ] InjCode F a b ∥₁` only if that
-- Σ is an hProp, and that needs the CODE to be unique, not merely the
-- conjuncts to be propositions.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-576.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.Coding.Model {ℓ} using ( svAt; domAt )
open import L.Coding.Injection {ℓ} lem using ( injAt )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.Foundations.HLevels using ( isProp× )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- ---------------------------------------------------------------------
-- W3 ITSELF.  Four conjuncts (src/L/Cardinal.lagda.md:224-228): three
-- satisfaction facts, each `⟨ _ ⟩` of an hProp, and one Π whose
-- codomain is `⟨ _ ∈ _ ⟩`.  Every one of them is a proposition, so the
-- product is.
-- ---------------------------------------------------------------------

isPropInjCode : (F a b : S) → isProp (InjCode F a b)
isPropInjCode F a b =
  isProp× (snd ((F ∷ a ∷ []) ⊨ svAt zero))
   (isProp× (snd ((F ∷ a ∷ []) ⊨ domAt zero (suc zero)))
    (isProp× (snd ((F ∷ a ∷ []) ⊨ injAt zero))
     (isPropΠ λ x → isPropΠ λ y → isPropΠ λ _ → snd (fst y ∈ fst b))))

-- ---------------------------------------------------------------------
-- AND THE QUESTION THE ROUTE TURNS ON, TYPE ONLY.  NOT INHABITED HERE.
-- ---------------------------------------------------------------------

CodeUnique : Type (ℓ-suc ℓ)
CodeUnique = (a b : S) → isProp (Σ[ F ∈ S ] InjCode F a b)
