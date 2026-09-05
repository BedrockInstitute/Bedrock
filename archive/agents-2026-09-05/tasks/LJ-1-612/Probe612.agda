{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.612]  THE REHOMING DEFECT, REPAIRED AT ITS OWN SITE.
--
-- [LJ-1.607] found the defect while doing something else and called
-- it cheap (agents/tasks/LJ-1-607/lj-1.607-report.md:200-205): a
-- rehomed probe whose top module name predates [LJ-1.142] cannot be
-- imported through the library as-is.  The file sits one directory
-- below the library's include root agents/tasks (bedrock.agda-lib:
-- `include: src agents/tasks`) while its declared top module name
-- (agents/tasks/LJ-1-136/ProbeLJ1136B.agda:35) still spells the flat
-- pre-rehome name ProbeLJ1136B.  The symptom, re-measured at THIS
-- tree, is runs/w3-1.out; [LJ-1.607]'s copy is
-- agents/tasks/LJ-1-607/runs/p136-1.out:5-15.
--
-- THE CURE USED HERE IS THE FLAGS, NOT A COPY.  This file is run
-- with `-i agents/tasks/LJ-1-136 -i agents/tasks/LJ-1-134`, which
-- restores the probe's pre-rehome include context in place.  The
-- probe file is untouched and no line of it is duplicated anywhere:
-- the copy way is [LJ-1.607]'s runs/cold/, and R-42
-- (dev/LESSONS.md:4882) prices carrying one object across two files
-- at 155.02 s against 1.74 s.  Why the library path itself
-- (`LJ-1-136.ProbeLJ1136B`) cannot be the fix instead: measured at
-- runs/dot-1.out.  The section THE SYMPTOM AND THE CURE in
-- lj-1.612-report.md states both cures at file:line.
--
-- THE REHOMED PROBE CHOSEN IS [LJ-1.136]'s ProbeLJ1136B, the file
-- [LJ-1.607] re-measured: pick-canonical at
-- agents/tasks/LJ-1-136/ProbeLJ1136B.agda:114-116 and discharge at
-- :146-148.  Its dependency ProbeLJ1134A
-- (agents/tasks/LJ-1-134/ProbeLJ1134A.agda:21) is rehomed the same
-- way and is imported by it, so the second -i root is part of the
-- cure, not decoration.
--
-- One agda process at a time.  The caliber is the program's, on
-- this pane; nothing in this file sets it.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import FOL.ZFStructure using ( module hPropStructure )

module LJ-1-612.Probe612 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

  open import L.Constructible {ℓ} using ( IsOrd; 𝒮ʟ )
  open hPropStructure 𝒮ʟ using ( S )

  -- THE REHOMED PROBE, IMPORTED BY ITS PRE-REHOME TOP NAME.  Without
  -- the -i flags this line is the symptom itself: [FileNotFound],
  -- runs/w3-1.out.  With them it resolves to
  -- agents/tasks/LJ-1-136/ProbeLJ1136B.agda in place.
  open import ProbeLJ1136B lem

  module At (β : V ℓ) (oβ : IsOrd β) (D C : S) where

    open Sel β oβ D C

    -- THE OBLIGATION.  Imported and used: the term on the right is
    -- pick-canonical, the probe's own, defined at
    -- agents/tasks/LJ-1-136/ProbeLJ1136B.agda:114-116 and re-ascribed
    -- HERE through the library-context import above.  Not re-typed:
    -- its body is the probe's, untouched in its own file.
    rehomed-import-works : (h₁ h₂ : Ne) → pick h₁ ≡ pick h₂
    rehomed-import-works = pick-canonical
