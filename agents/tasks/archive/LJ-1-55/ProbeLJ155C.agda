{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.55] probe C: the WitnessAgree building blocks.  Test whether
-- the closedness relation bodies are definitionally the same formula
-- on both sides, and whether the frame shapes transfer at the
-- closedness frames.
--
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ155C {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import FOL.Absoluteness
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∧̇_; _∈̇_; _⇒̇_; ∃̇∈; ∀̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ}
  using ( bothSameAt; oneSameAt; oneSuccAt; succSndAt
        ; binShapeAt; unShapeAt; domAt; inDomAt; appAt; appAt-adequate )
open import L.Condensation {ℓ} lem using
  ( bothSameB; oneSameB; oneSuccB; succSndB
  ; domB; closedBS; hasWitnessBS; extAtB )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.Data.Nat using ( _+_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- The relation bodies: the same formula on both sides?
bothSame-eq : ∀ {m} (C : Fin m) → bothSameB C ≡ bothSameAt C
bothSame-eq C = refl

-- oneSameB READ appAt (suc^3 C) (suc^2 zero) (suc zero) at the 3-deep
-- frame a ∷ ar ∷ c ∷ γ: the pair (c, ar).  oneSameAt C reads
-- appAt (suc^3 C) (suc zero) zero: the pair (ar, a).  The story read
-- the code slot where the machine reads the argument slot, so the two
-- were NOT definitionally equal.  [LJ-1.55] found it; the orchestrator
-- verified it against the frame comment at Condensation:1500 and
-- against the three sibling frames, and cured it at Condensation:1549.
-- This refl is the cure's consumer test, and it is the check the
-- eight-frame closedness transfer needs.
oneSame-eq : ∀ {m} (C : Fin m) → oneSameB C ≡ oneSameAt C
oneSame-eq C = refl

-- oneSuccB/succSndB carry the bounded existential (∃̇∈ with a
-- K-membership witness) where the machine's oneSuccAt/succSndAt carry
-- the unbounded ∃̇; the bodies agree (sucAtL/appAt with the same
-- indices).  The refl tests fail on the quantifier only, as expected.

-- =====================================================================
-- THE DOMAIN TRANSFER: domB f d K against domAt f d.
-- The story bounds the domain element x by K and the witness y by K;
-- the machine leaves both unbounded.  So the story side is strictly
-- WEAKER: domB f d K says "x in K -> (x in dom f <-> x in d)", domAt
-- f d says it for every x.  The machine-to-story direction is
-- provable under a site fact giving the witness y in K.  The
-- story-to-machine direction needs every domain element in K (a
-- universal xK hypothesis), which no site fact supplies; at the
-- generic frame it is false.  The graph frame must supply the
-- missing membership from its own bounded quantifiers.
-- =====================================================================
module DomAgree {m : ℕ} (f d K : Fin m) (γ : S ^ m)
  (yK : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩
      → ⟨ fst y ∈ fst (lookup K γ) ⟩) where

  out : ⟨ γ ⊨ domAt f d ⟩ → ⟨ γ ⊨ domB f d K ⟩
  out h = λ x xK →
      ( λ hx → h x .fst
          (PT.rec squash₁ (λ { (y , (_ , p)) → ∣ y , p ∣₁ }) hx) )
    , ( λ hx → PT.rec squash₁
          (λ { (y , p) →
            ∣ y , ( yK x y
                     (subst ⟨_⟩ (appAt-adequate (suc (suc f)) (suc zero) zero
                       (y ∷ x ∷ γ)) p)
                 , p ) ∣₁ })
          (h x .snd hx) )
