{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.566]  W3.  DO THE FOUR CONJUNCTS SHARE ONE `F`?
--
-- The brief names this the widest unmeasured term and orders it written
-- FIRST and typechecked ALONE.  It is TYPE ONLY: every binding below is
-- a name for a carve a predecessor already built, and nothing is proved.
--
-- THE FRAME IS `[LJ-1.529]`'s, and the report says why: `[LJ-1.529]` is
-- the one predecessor whose obligation names BOTH an `F` and a `b`
-- (Probe529.agda:282-285), so it is the only frame that fixes the whole
-- of `InjCode`'s telescope.
--
-- `injAt` HAS NO ROW HERE BECAUSE IT HAS NO TERM.  `[LJ-1.531]` says so
-- itself (lj-1.531-report.md:34, Probe531.agda:52); it delivered
-- `rank-at′-inj`, which names no `F`.  So the fourth name below is the
-- frame `injAt` MUST be built at, and not a frame it was built at.
--
-- This file measures the FLOOR: the import set, with the four names and
-- no proof.  runs/Unify.agda then asks whether the three that exist
-- unify.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-566.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )

import LJ-1-524.Probe524 {ℓ} lem as P524
import LJ-1-529.Probe529 {ℓ} lem as P529
import LJ-1-559.Probe559 {ℓ} lem as P559

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

-- the four conjuncts' F, stated side by side at one frame, TYPE ONLY

F-of-svAt : (a : S) (oa : IsOrd (fst a)) → S
F-of-svAt a oa = P524.Carve.G a oa (P529.Bound′.bnd a oa)

F-of-domAt : (a : S) (oa : IsOrd (fst a)) → S
F-of-domAt a oa = P559.Carve.G a oa

F-of-range : (a : S) (oa : IsOrd (fst a)) → S
F-of-range a oa = P529.Carve.G a oa

-- `injAt` was NOT delivered.  This is the frame it must be built at.
F-of-injAt : (a : S) (oa : IsOrd (fst a)) → S
F-of-injAt a oa = P529.Carve.G a oa

-- and the codomain, which only `[LJ-1.529]` names
b-of-range : (a : S) (oa : IsOrd (fst a)) → S
b-of-range a oa = P529.Carve.C a oa
