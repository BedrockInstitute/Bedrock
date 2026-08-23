{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.547]  W3: THE DELIVERED TYPE, IMPORTED AND ASCRIBED AT ITSELF.
--
-- The brief names the widest unmeasured term:
--
--   -- LJ-1.566's injcode-assembled, imported, ascribed at ITS OWN
--   -- type, TYPE ONLY
--
-- and orders it written FIRST and typechecked ALONE.  This file is
-- that.  It inhabits nothing and derives nothing: the one term below
-- is [LJ-1.566]'s own, and the one line of code ascribes it at a type
-- written out longhand in THIS file.  If the longhand type and the
-- imported term's own type are not the same type on the nose, this
-- file does not typecheck.  That is the whole measurement.
--
-- ONE SPELLING, AND NO BRIDGE.  `P566.Carve.G` and `P566.Carve.C` are
-- [LJ-1.566]'s own names for the carve and its bounding ordinal
-- (Probe566.agda:316-334).  No second spelling of the carve appears
-- anywhere in this file, so no conversion between spellings is ever
-- asked for.  That is R-42's cure (dev/LESSONS.md, R-42) and it is the
-- reason this file is seconds where the old plan's frames were not.

open import Base.Prelude
open import Base.Classical using ( LEM )

module LJ-1-547.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Cardinal {ℓ} lem using ( InjCode )

import LJ-1-566.Probe566 {ℓ} lem as P566

open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
--  THE TYPE, LONGHAND.  Binders and head exactly as [LJ-1.566] wrote
--  them at Probe566.agda:492-495; `F` and `b` spelled through the
--  import at the spelling its proof produces.
-- =====================================================================

w3-type-only :
    (a : S) (oa : IsOrd (fst a))
  → InjCode (P566.Carve.G a oa) a (P566.Carve.C a oa)
w3-type-only = P566.injcode-assembled
