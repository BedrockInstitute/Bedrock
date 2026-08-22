{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.554] W3.  THE ARITY-3 SATISFACTION READING ITSELF.
-- TYPE ONLY.  No inhabitant, no separation, no adequacy.  This slice
-- is typechecked ALONE, before any other Agda of this task, exactly as
-- the brief ordered.
--
-- WHAT THE BRIEF ASKED.  "If the reading will not even form away from
-- [LJ-1.549]'s frame, the task is about a different statement and you
-- must say so before spending the estimate."
--
-- SO THE QUESTION IS NARROW: does
--
--     ⟨ (y ∷ x ∷ z ∷ []) ⊨ Link ⟩
--
-- form for an ABSTRACT `Link : Formula S 3`, with no `[LJ-1.549]`
-- import, no `powL`, no `prAtL`, and no assignment?  Everything below
-- the imports is that one question.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-554.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- ==================================================================
-- THE READING.  IT FORMS, AND IT FORMS AT ARITY 3 WITH NOTHING ELSE
-- IN SCOPE.
--
--     var 0  =  y, the value
--     var 1  =  x, the argument
--     var 2  =  z, the pair slot
--
-- The environment `(y ∷ x ∷ z ∷ [])` is a vector `S ^ 3`, so the
-- arity of `Link` and the length of the environment are the SAME
-- number by construction: a mismatch is unrepresentable, not
-- forbidden.
-- ==================================================================

Reading : Formula S 3 → S → S → S → Type (ℓ-suc ℓ)
Reading Link y x z = ⟨ (y ∷ x ∷ z ∷ []) ⊨ Link ⟩

-- AND IT IS A PROPOSITION, which is what the two readings of
-- `[LJ-1.549]`'s `Residue` silently need: `link-out` eliminates from
-- it into a path, and an elimination out of a truncated satisfaction
-- is legal only at a proposition-valued goal.
Reading-isProp : (Link : Formula S 3) (y x z : S) → isProp (Reading Link y x z)
Reading-isProp Link y x z = snd ((y ∷ x ∷ z ∷ []) ⊨ Link)

-- THE TWO READINGS OF THE BRIEF, AS TYPES AND NOTHING MORE.  They are
-- written here at an ABSTRACT assignment `v : S → S` and an abstract
-- membership `P`, so that this slice depends on no `[LJ-1.549]` term.
LinkIn : Formula S 3 → (S → Ω) → (S → S) → Type (ℓ-suc ℓ)
LinkIn Link P v = (x y z : S) → ⟨ P x ⟩ → fst y ≡ fst (v x) → Reading Link y x z

LinkOut : Formula S 3 → (S → Ω) → (S → S) → Type (ℓ-suc ℓ)
LinkOut Link P v = (x y z : S) → Reading Link y x z → ⟨ P x ⟩ → fst y ≡ fst (v x)
