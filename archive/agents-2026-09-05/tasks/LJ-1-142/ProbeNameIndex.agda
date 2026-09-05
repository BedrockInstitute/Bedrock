{-# OPTIONS --cubical --safe #-}

-- [LJ-1.142] THE DIRECTORY-NAME LEGALITY CHECK.
--
-- `bedrock.agda-lib` reads `include: src agents/tasks`, so a DIRECTORY under
-- that root becomes a module name component. Each import below resolves one
-- directory-name shape that the [LJ-1.142] layout produces:
--
--   NAMETEST-L3-32-T126      capitals, digits and dashes (the retired-route shape)
--   NAMETEST-Geology-Legacy  mixed case, no numeric code
--   nametest-lowercase       all lower case (the `archive` level)
--
-- If one shape does not parse as an Agda name, this file is RED.
-- The two NEGATIVE controls are the sibling directories `NAMETEST-L3.32-DOT`
-- and `NAMETEST-L3_32_UNDERSCORE`. They are NOT imported here because they do
-- not typecheck; run agda on them directly to see the two failure modes.
module LJ-1-142.ProbeNameIndex where

open import LJ-1-142.NAMETEST-L3-32-T126.ProbeName1
open import LJ-1-142.NAMETEST-Geology-Legacy.ProbeName2
open import LJ-1-142.nametest-lowercase.ProbeName3
