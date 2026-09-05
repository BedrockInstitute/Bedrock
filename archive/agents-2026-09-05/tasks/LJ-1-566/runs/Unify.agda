{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.566]  W3, PART TWO.  THE THREE `F`s THAT EXIST: DO THEY UNIFY?
--
-- runs/W3.agda names them side by side and proves nothing.  This file
-- asks the elaborator the question, at the `S` level and NOT yet inside
-- a satisfaction predicate.  `refl` is the whole of each proof, so a
-- green run says the three spellings are definitionally one carve, and a
-- red run says the coding leg has a seam and names it.
--
-- THIS IS THE CHEAP HALF OF THE QUESTION.  `[LJ-1.524]`'s price finding
-- (Probe524.agda:160-178) is about a comparison INSIDE `_⊨_`, which
-- recurses on the formula and forces the carve to constructor form.
-- runs/Transport.agda asks that one.  The two are separated so that a
-- wall names which comparison hit it.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-566.runs.Unify {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )

import LJ-1-524.Probe524 {ℓ} lem as P524
import LJ-1-529.Probe529 {ℓ} lem as P529
import LJ-1-559.Probe559 {ℓ} lem as P559

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

-- 1.  `[LJ-1.524]`'s carve, at the bound `[LJ-1.529]` built, IS
--     `[LJ-1.529]`'s carve.  The two differ by one rebuilt `rank-graph`
--     and one rebuilt `ordQ`.
svAt-F-is-range-F :
    (a : S) (oa : IsOrd (fst a))
  → P524.Carve.G a oa (P529.Bound′.bnd a oa) ≡ P529.Carve.G a oa
svAt-F-is-range-F a oa = refl

-- 2.  `[LJ-1.559]`'s carve IS `[LJ-1.529]`'s.  These two differ by a
--     rebuilt `rank-graph`, a rebuilt `ordQ` AND a rebuilt `Bound′`
--     (Probe559.agda:108-137 against Probe529.agda:101-131, byte
--     identical bodies).
domAt-F-is-range-F :
    (a : S) (oa : IsOrd (fst a))
  → P559.Carve.G a oa ≡ P529.Carve.G a oa
domAt-F-is-range-F a oa = refl

-- 3.  and the bounds themselves, which is the deepest of the three
svAt-bnd-is-domAt-bnd :
    (a : S) (oa : IsOrd (fst a))
  → P559.Bound′.bnd a oa ≡ P529.Bound′.bnd a oa
svAt-bnd-is-domAt-bnd a oa = refl
