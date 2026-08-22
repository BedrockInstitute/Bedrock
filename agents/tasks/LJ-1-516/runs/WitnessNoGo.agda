{-# OPTIONS --cubical --safe --guardedness #-}

-- The witness meter of amendment A1, reproduced locally in the form
-- scripts/pod/witness.py derives (witness_source, :262-282): the term
-- reference `witness = Target.<name>`, not an `open ... using`.
--
-- THE BRIEFED NAME IS DELIBERATELY ABSENT.  This task states a NO-GO at
-- graphSat-transports and writes no term for it.  This file records what
-- the meter sees, so the critic can tell an absent term from a broken
-- probe.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-516.runs.WitnessNoGo {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import LJ-1-516.Probe516
module Target = LJ-1-516.Probe516 {ℓ} lem

-- MEASURED AND KEPT AS A COMMENT, in [LJ-1.514]'s protocol.  The line
-- below is the meter's own derivation at the briefed name.  It FAILS:
-- runs/witness-nogo.out:3-8, [NotInScope] on Target.graphSat-transports,
-- exit 42.  Agda's own suggestion in that output is the TYPE this task
-- delivers without a term.  The line stays commented so the file is green
-- while the task runs, and the run output is the evidence.
--
-- witness = Target.graphSat-transports

-- What the meter DOES find at the briefed obligation: a type, not a term.
witness = Target.GraphSatTransports
