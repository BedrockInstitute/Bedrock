{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.547]  THE BOOKKEEPING CLOSE: IMPORT AND BIND, NOT RE-PROVE.
--
-- The obligation `injcode-assembled` was DELIVERED by [LJ-1.566]
-- (agents/tasks/LJ-1-566/Probe566.agda:492-500), GO at a measured
-- 1.67 s floor and 9.66 s finish (agents/tasks/LJ-1-566/
-- lj-1.566-report.md, `## THE FLOOR AND THE FINISH`).  This task's
-- first attempt restated the four conjuncts over its own carve and
-- its acceptance re-run never finished inside the deadline; the owner
-- authorized closing the row by importing the delivered term.  This
-- file re-derives nothing and proves nothing.  The mathematics is
-- [LJ-1.566]'s; the claim of this file is only that the delivered
-- term, imported, binds the name this task owes.
--
-- THE D-10 WAS DONE BEFORE THIS AGDA (lj-1.547-report.md,
-- `## D-10, THE TYPE COMPARISON`): the delivered type and this task's
-- old type are the same obligation at the same frame, the binders and
-- the head are identical, and the only difference is which file's own
-- ONE local module spells the carve.  There is no bridge to build and
-- none was built.
--
-- ONE SPELLING, R-42's CURE (dev/LESSONS.md, R-42): every carve name
-- below is `P566.Carve`, the spelling [LJ-1.566]'s own proof
-- produces.  The type says the name and never the body, and no second
-- spelling of the carve appears in this file, so the elaborator is
-- never asked to convert one spelling into another.  `runs/W3.agda`
-- is the same ascription alone, typechecked FIRST and green at 2.06 s
-- (`runs/w3type-1.out`).

open import Base.Prelude
open import Base.Classical using ( LEM )

module LJ-1-547.Probe547 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Cardinal {ℓ} lem using ( InjCode )

import LJ-1-566.Probe566 {ℓ} lem as P566

open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
--  THE OBLIGATION.  One name, bound by import at [LJ-1.566]'s own
--  type: the binders `(a : S) (oa : IsOrd (fst a))`, the head
--  `InjCode`, the `a` in the middle, and `F` and `b` at
--  `P566.Carve.G` and `P566.Carve.C`, are Probe566.agda:492-495
--  spelled through the import.  The elaborator checks the written type
--  against the imported term at ONE spelling; nothing unfolds across
--  files and no conversion is asked for.
-- =====================================================================

injcode-assembled :
    (a : S) (oa : IsOrd (fst a))
  → InjCode (P566.Carve.G a oa) a (P566.Carve.C a oa)
injcode-assembled = P566.injcode-assembled
