{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.343] EVERY CONSUMER OF THE REPAIRED CHAPTER, CHECKED.
--
-- `grep -rn "L.Condensation" src/` gives FIVE masters that import the
-- chapter, plus src/Everything.lagda.md:378, which the orchestrator
-- checks.  This file imports all five, so ONE agda process typechecks
-- every direct consumer against the repaired interface.
--
-- WHY A RUN AND NOT A READING.  No `using` list of the five names
-- `DefinesAgree`, `LeafAgree`, `envK`, `pairK` or `defPairK`, so a break
-- is structurally impossible.  C-45 is exactly the law that says a
-- reading of a telescope is not a check of it, so this file runs.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

module LJ-1-343.ConsumerCheck343 where

import L.BoundedSubset
import L.Coding.EnvSupply
import L.Condensation.LowerAgree
import L.Condensation.UpperAgree
import L.Condensation.TwelveAgree
