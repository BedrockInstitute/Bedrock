{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.624]  THE WARM FLOOR, W3 OF THE LANDING BRIEF, MEASURED FIRST.
--
-- The eleven `src` interfaces warm, one trivial term. The import list is
-- byte-identical to `agents/tasks/LJ-1-619/Probe619.agda:17-31`, the floor
-- file `[LJ-1.622]` ran, so this number is comparable with its floor
-- (agents/tasks/LJ-1-622/runs/floor.out) inside the same tier. ONE fresh
-- Agda process, the pane's own caliber, never set here.
--
-- Recipe test (agents/tasks/LJ-1-622/lj-1.622-report.md, item 3): about
-- 766 MB and 3 s means proceed; far higher means the wall is in this
-- worktree's `_build` and the build state must be bisected, not the term.
--
-- Nothing is postulated.  Nothing lands in `src/`.

module LJ-1-624.Probe624 where

open import Base.Prelude

import L.Cardinal
import L.BoundedSubset
import L.CantorBernstein
import L.InjChain
import L.Ordinal.Stages
import L.Ordinal.Linear
import L.Constructible
import L.Ordinal
import V.Model
import V.Presentation
import V.Hierarchy

floor624 : Type → Type
floor624 A = A
