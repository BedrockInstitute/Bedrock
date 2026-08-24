{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.624]  THE ONE AGGREGATOR LINE, AT ITS NARROWEST DECISIVE SHAPE.
--
-- `src/Everything.lagda.md` gains exactly one line, `import
-- L.CardinalAbove`.  The whole-tree typecheck of that file exhausts the
-- wide-tier 2 g cap (runs/typecheck-everything.out), which is a caliber
-- property of the whole tree, not of the one line.  This file is the
-- narrow check that the line resolves: the module path, the module
-- name and the bare import itself.  It is a measurement, and it lands
-- nothing in src/.
--
-- Nothing is postulated.

module LJ-1-624.runs.ImportCheck624 where

import L.CardinalAbove
