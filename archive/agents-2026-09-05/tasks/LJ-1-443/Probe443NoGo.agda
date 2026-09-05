{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.443] STATED NO-GO.  The brief names src/L/StageBound.lagda.md
-- as the home of bounded-modulo-collect.  That file is not in this
-- tree.  The import is the measurement of that absence.
--
-- W3 is Probe443.agda and was typechecked ALONE, obligation omitted.
-- This file is not that measurement.  It is the obstruction the
-- branch no-go-stated needs: Agda over the named home, exit 42.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

module LJ-1-443.Probe443NoGo where

open import L.StageBound
