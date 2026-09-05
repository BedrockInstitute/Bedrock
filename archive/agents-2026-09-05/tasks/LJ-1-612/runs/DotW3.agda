{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.612]  THE LIBRARY-PATH VARIANT.  Does importing the rehomed
-- probe by its path name through the library (no -i flags, no copy)
-- close the defect?  The file is found under agents/tasks/; the
-- question is whether the flat declaration at
-- agents/tasks/LJ-1-136/ProbeLJ1136B.agda:35 survives the longer name.
-- Measured at runs/dot-1.out.

module LJ-1-612.runs.DotW3 where

  import LJ-1-136.ProbeLJ1136B
