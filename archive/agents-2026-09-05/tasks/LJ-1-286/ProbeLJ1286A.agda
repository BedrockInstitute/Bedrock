{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.286] PROBE A.  RE-DERIVE the discharge before the edit (premise 1).
--
-- The brief says `absorbs` supplies `AbsorbsShape` on the nose, and cites
-- agents/tasks/LJ-1-284/ReRun.agda:92-93 for it.  This file re-derives that
-- claim independently, against the UNEDITED src/L/GCH.lagda.md, so the edit
-- rests on a measurement of mine and not on a prior report.
--
-- Two questions, both answered by the typechecker:
--   1  Is `absorbs` of type `AbsorbsShape`, with no `subst` and no wrapper?
--   2  Is `sq` (A5's `SqShape`) supplied by anything?  The brief says NO.
--      Question 2 is asked as a COMMENT below, never as a term: the brief
--      forbids attempting the second discharge.
--
-- Tracked; ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-286.ProbeLJ1286A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import L.GCH {ℓ} lem using ( AbsorbsShape )
open import L.Absorption {ℓ} lem using ( absorbs )

-- THE ONE LINE.  No `subst`, no eta-expansion, no wrapper.  If the two
-- types differed by any conversion the elaborator cannot close, this file
-- would be red.
mine : AbsorbsShape
mine = absorbs

-- WHAT WAS NOT ATTEMPTED.  `SqShape` (src/L/GCH.lagda.md:44-47 after the
-- edit, :42-45 before it) is the square law uniform over the infinite
-- L-ordinals.  src/L/InjChain.lagda.md supplies only the base
-- `squareω : sq ω` at :184.  A uniform law DOES exist, at
-- src/L/Ordinal/SquareLaw.lagda.md:960, but it is `Init`-restricted and
-- `Init` is strictly stronger than `SqShape`'s hypotheses (report section
-- 5.1).  The brief forbids the attempt, so no term of `SqShape` is
-- written here.
