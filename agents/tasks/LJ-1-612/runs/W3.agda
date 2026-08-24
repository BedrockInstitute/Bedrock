{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.612]  W3, THE WIDEST UNMEASURED TERM.  The failing import
-- itself, nothing else: one rehomed probe's module, TYPE ONLY.
-- `ProbeLJ1136B` is the pre-[LJ-1.142] top name declared at
-- agents/tasks/LJ-1-136/ProbeLJ1136B.agda:35, one directory below
-- the library's include root agents/tasks.
--
-- Run WITHOUT the -i flags (w3-1.out): the symptom, re-measured here.
-- Run WITH them (w3-2.out): the flag cure, this file re-checked.
-- The header spells the path name: a headerless file is refused by
-- Agda before it reaches the import (runs/w3-1.out, first attempt,
-- [ModuleNameDoesntMatchFileName]), which is the same wall the
-- rehomed probe's own flat declaration would hit if imported by its
-- path through the library (runs/dot-1.out).

module LJ-1-612.runs.W3 where

  import ProbeLJ1136B
