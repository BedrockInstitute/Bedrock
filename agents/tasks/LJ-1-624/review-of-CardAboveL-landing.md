# Review of the `CardAboveL` landing: the corrected obligation is discharged

**VERDICT: GO. The obligation this review corrected on 2026-08-19 is now in
the tree at the corrected name, `src/L/CardinalAbove.lagda.md::CardAboveL`,
and the scope defect that stranded the first landing is fixed, because
`[LJ-1.624]`'s brief names both write paths.**

The term and its statement are byte-identical to
`agents/tasks/LJ-1-528/Probe528.agda:638-643`, and the statement was not
weakened by one hypothesis: the telescope is `{ℓ : Level}
(lem : LEM (ℓ-suc ℓ))` and nothing else
(`src/L/CardinalAbove.lagda.md:18`).

## WHAT IS IN THE TREE NOW

- `src/L/CardinalAbove.lagda.md`, new, 586 lines, a leaf master (nothing
  imports it, so it adds no import edge to any existing chapter). The
  declaration is at `:580`, the term `CardAboveL = noInjOrd→CardAboveLᵀ
  noInjOrd` at `:585`. Green: `agda src/L/CardinalAbove.lagda.md` in one
  fresh process under the pane's `-A64m -I0 -M2g`, exit 0, 4.16 s, peak RSS
  933,462,016 bytes (43.5 percent of cap), `agents/tasks/LJ-1-624/runs/typecheck-chapter.out`.
- `src/Everything.lagda.md`, one line added at `:397`, `import
  L.CardinalAbove`, after `import L.StageBound` (`:396`). Nothing reordered.
  The bare import resolves: one-line check, exit 0, 3.02 s,
  `agents/tasks/LJ-1-624/runs/import-check.out`.

## WHAT THE THREE FAILURES WERE, NOW MEASURED

1. `[LJ-1.555]`: green in its worktree, absent from the branch, because the
   scope named neither path. Fixed by this brief's scope; both paths landed.
2. `[LJ-1.599]` and `[LJ-1.616]`: silent heap walls at 18.79 s and 19.32 s.
   `[LJ-1.624]` reproduced the signature in a warm worktree that has no
   reason to be cold: `agda src/Everything.lagda.md`, the whole tree, under
   the wide tier's 2 g cap, exhausts the heap in 19.18 s, exit 251, peak
   1,880,276,992 bytes, `agents/tasks/LJ-1-624/runs/typecheck-everything.out`,
   without importing `[LJ-1.526]`'s probe and without running `make check`.
   The cause the predecessors left silent is a TIER property: the whole
   tree is a HEAVY-tier object and the landing pane is WIDE. The master
   itself peaks at 43.5 percent of the wide cap and lands.

## WHAT THIS REVIEW ASKED FOR, ANSWERED

- Name the file and the statement: done, at the corrected name.
- A scope that can commit the result: the brief names
  `src/L/CardinalAbove.lagda.md` and `src/Everything.lagda.md`; rule R8 can
  commit both.
- No weakening: the statement is the probe's, byte for byte.

## WHAT REMAINS OPEN, OUT OF THIS SCOPE

1. The duplication: the same term now exists at
   `agents/tasks/LJ-1-528/Probe528.agda:638-643` and in the tree, and
   nothing makes the two agree. The one-line cure is in the
   `[LJ-1.555]` report (WHAT MOVED AND WHAT DID NOT).
2. `cardAboveAnyOrd`, the stronger statement, is free at ten lines over the
   landed content (`agents/tasks/LJ-1-528/Probe528.agda:669-678`).
3. A whole-tree green in this campaign must be priced under the cap that
   can carry it; the wide pane cannot run one, and the Makefile's own
   default is `-M16g` (`Makefile:20`).
