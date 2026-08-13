{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.141] probe A: a probe runs from its per-task directory.
--
-- The owner ruled on 2026-08-13 that a probe pairs one-to-one with its report,
-- lives with it, is tracked, is never deleted, and that a task's probes go in a
-- directory of their own.  This file IS that layout:
--
--     agents/reports/lj-1.141-report.md        the report
--     agents/reports/LJ-1-141/ProbeLJ1141A.agda   its probes
--
-- What it measures, and it measures only this:
--
-- 1. `bedrock.agda-lib` accepts a SECOND include root whose path carries a
--    separator (`agents/reports`).  [LJ-1.138] measured two roots in /tmp with
--    single-component names; a path with a `/` was never measured here.
-- 2. A module under the second root imports the tower under the FIRST root.
--    `Base.Prelude` and `L.Stage` both live under `src/`.
-- 3. The per-task directory becomes the module QUALIFIER, so this file must
--    declare `module LJ-1-141.ProbeLJ1141A`.  That is the whole cost of the
--    per-task layout for a NEW probe: one line, written once, by the agent.
--
-- WHY THE DIRECTORY IS `LJ-1-141` AND NOT `lj-1.141`.  A directory under an
-- include root becomes a module name component, so it must parse as an Agda
-- name.  MEASURED 2026-08-13, all four in Agda 2.8.0:
--
--     LJ-1-141   OK           a dash does not split a name
--     lj-1.141   ParseError   `.` splits the qualifier; `141` is then a literal
--     LJ-1_141   ParseError   `_` splits a mixfix name; `141` is then a literal
--     LJ_1_141   ParseError   same
--
-- The verdict is section 1 of `agents/reports/lj-1.141-report.md`.

module LJ-1-141.ProbeLJ1141A where

open import Base.Prelude
open import L.Stage using ()

-- A body, so the file is not an empty import list.
_ : Level
_ = ℓ-zero
