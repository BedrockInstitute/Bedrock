{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.361] MINIATURE.  Is the one bounded separation the Tarski
-- fixed-point Cantor-Bernstein needs a FIELD of the generic model
-- record, available at an ABSTRACT ZFStructure with no model-specific
-- input?
--
-- WHAT THIS FILE DECIDES.  The bad set of the fixed-point argument is
-- carved from a by one formula: x lies in a closed subset of a, where
-- the closed subsets are collected by a bounded quantifier over the
-- members of the power object.  The miniature builds that formula
-- shape at an ABSTRACT structure, with a, b, F, G as parameters
-- (constants) and the closure condition left abstract, then obtains
-- the carved set through `separate`, the operation derived from the
-- `hasSeparation` field alone.
--
-- The closure condition is left abstract because its CONTENT (the
-- pair readers spelling "g (f z) = y") is priced by [LJ-1.353] row 2
-- and is not what this file decides.  What this file decides is the
-- CONTAINER: any Formula S 1 whatsoever, with any constants and any
-- bounded quantifiers, reaches the field.  If this types, the owner's
-- route is open at the record level.
--
-- Bonus: the definitional-unfold check shows satisfaction of the
-- bounded quantifier computes to the truth algebra's sup with no
-- translation layer, which is what makes the internal proof body
-- tractable at an abstract carrier.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )

module LJ-1-361.MiniSep {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open TruthAlgebra (hPropAlgebra ℓ) using ( ⋁; _⊓_ )

open import FOL.Syntax
  using ( Term; var; con; Formula
        ; _∈̇_; _∧̇_; _∨̇_; _⇒̇_; _≐_; ∀̇_; ∃̇_; ∀̇∈; ∃̇∈ )
import FOL.ZFModel
open hPropStructure 𝒮 using ( S; _∈ˢ_ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open At S id using ( _⊨_ )

module ZF = FOL.ZFModel 𝒮

-- The Tarski separation, at an abstract model.  Parameters a b F G are
-- sets of the model; closedAt is the closure condition with variable
-- zero the candidate subset X (the second slot is unused by it here,
-- kept so the shape matches the real formula, which reads x too).
module Tarski (mod : ZF.isZFModel) (a b F G : S)
              (closedAt : Formula S 2) where

  open ZF.isZFModel mod using ( separate; separate-spec; 𝒫 )

  -- the one formula the fixed-point argument separates along:
  -- x ∈ X for some closed X ⊆ a, X collected over members of 𝒫 a.
  tarskiFo : Formula S 1
  tarskiFo = ∃̇∈ (con (𝒫 a))
           ( (var (suc zero) ∈̇ var zero) ∧̇ closedAt )

  -- the carved set, from the field alone
  bad : S
  bad = separate a tarskiFo

  -- its specification, literally the projection of the field
  bad-spec = separate-spec a tarskiFo

  -- satisfaction of the bounded quantifier computes definitionally to
  -- the truth algebra's sup: no translation layer, so a proof body at
  -- this abstract carrier manipulates it as plain host logic.
  unfold : (x : S)
         → ( (x ∷ []) ⊨ tarskiFo )
         ≡ ⋁ S (λ X → (X ∈ˢ 𝒫 a)
                    ⊓ ((X ∷ x ∷ []) ⊨ ((var (suc zero) ∈̇ var zero) ∧̇ closedAt)))
  unfold x = refl
