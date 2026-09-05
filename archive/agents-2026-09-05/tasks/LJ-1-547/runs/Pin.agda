{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.547]  THE PIN.  The obligation stated AGAIN, with no name of
-- Probe547's own synonyms, and inhabited by `injcode-assembled` and by
-- nothing else.
--
-- WHAT IT RULES OUT.  Probe547 defines `SvAtOf`, `DomAtOf`, `InjAtOf`
-- and `RangeOf` and assembles `InjCode` out of them.  If any one of the
-- four synonyms had drifted from `InjCode`'s component
-- (src/L/Cardinal.lagda.md:223-228), Probe547's own projections would
-- catch it; this file catches the other direction, that the DELIVERED
-- term supplies the four conjuncts written out longhand, at ONE `F`,
-- ONE `a` and ONE `b`, with `InjCode` never named on the left.
--
-- The right-hand side is one name.  Nothing is re-proved here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-547.runs.Pin {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Coding.Model {ℓ} using ( svAt; domAt )
open import L.Coding.Injection {ℓ} lem using ( injAt )
open import Cubical.Data.FinData using ( zero; suc )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

import LJ-1-547.Probe547 {ℓ} lem as P547

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

pinned :
    (a : S) (oa : IsOrd (fst a))
  → ⟨ (P547.Asm.G a oa ∷ a ∷ []) ⊨ svAt zero ⟩
  × ⟨ (P547.Asm.G a oa ∷ a ∷ []) ⊨ domAt zero (suc zero) ⟩
  × ⟨ (P547.Asm.G a oa ∷ a ∷ []) ⊨ injAt zero ⟩
  × ((x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (P547.Asm.G a oa) ⟩
               → ⟨ fst y ∈ fst (P547.Asm.C a oa) ⟩)
pinned = P547.injcode-assembled
