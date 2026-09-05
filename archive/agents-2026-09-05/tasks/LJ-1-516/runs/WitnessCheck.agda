{-# OPTIONS --cubical --safe --guardedness #-}

-- The witness meter of amendment A1, reproduced locally in the form
-- scripts/pod/witness.py derives (witness_source, :262-282): the term
-- reference `witness = Target.<name>`, not an `open ... using`.
--
-- THE BRIEFED NAME IS DELIBERATELY ABSENT.  `witness = Target.graphSat-transports`
-- does not resolve, because this task states a NO-GO at that type and writes
-- no term for it.  What IS delivered resolves from outside, and this file
-- proves that, so the critic can tell an absent term from a broken probe.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-516.runs.WitnessCheck {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

import LJ-1-516.Probe516
module Target = LJ-1-516.Probe516 {ℓ} lem

witness0 = Target.Gap.seam
witness1 = Target.Gap.transports-Δ₀
witness2 = Target.Gap.transports-Σ₁
witness3 = Target.no-Δ₀
witness4 = Target.no-Δ₀-lifted
witness5 = Target.no-Σ₁
witness6 = Target.no-Π₁
witness7 = Target.GraphSatTransports
