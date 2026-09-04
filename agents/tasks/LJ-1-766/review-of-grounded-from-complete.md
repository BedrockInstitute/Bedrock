# Review of `grounded-from-complete` (LJ-1.766): the brief's named factor does not exist

Task: LJ-1.766. Reviewer: coder. Evidence read: 2026-09-02.

## WHERE THE EVIDENCE LIVES

The `[LJ-1.765]` and `[LJ-1.765-SPLIT]` task directories are not in this
worktree. Their files sit in the program's own worktrees for those tasks,
`.pod-state/worktrees/LJ-1-765/` and `.pod-state/worktrees/LJ-1-765-SPLIT/`,
at the relative paths the brief's PREMISES use. Every citation below names
the path under one of those two roots, and every citation without one of
those two prefixes resolves in this worktree.

## THE VERDICT

**NO-GO, STATED BY THE BRIEF'S OWN STOP CLAUSE, BEFORE ANY RUN.** The brief
conditions its whole plan on one event: "This brief assumes
`[LJ-1.765-SPLIT]` GO. If that report is NO-GO, stop and do not inhabit
`amb` to fill the hole" (`agents/tasks/LJ-1-766/LJ-1.766.md:21`). The
report is NO-GO: "verdict: **NO-GO, AND IT IS NOT A RESOURCE WALL.** The
obligation's type, as the brief spells it, is UNINHABITED at its own
generality" (`agents/tasks/LJ-1-765-SPLIT/lj-1.765-SPLIT-report.md:10`).
The factor the brief consumes, `conv-at-Lδ`, was therefore never delivered,
and the tree carries a review that states why no body can exist
(`agents/tasks/LJ-1-765-SPLIT/review-of-conv-at-Lδ.md:7`). No probe was
built, no Agda process ran, nothing was inhabited, and `src/` is untouched.

## THE ORDER OF THE CLAUSES

The brief's plan has three steps in this order: consume `conv-at-Lδ` for
the Sigma's third component (`LJ-1.766.md:19`), stop if the split's report
is NO-GO (`:21`), floor first and then run (`:23`). Step two fired before
step one had an object to consume and before step three had anything to
price. The stop is not a judgement this slot makes; it is the instruction
at `LJ-1.766.md:21` executing on the measured verdict at
`lj-1.765-SPLIT-report.md:10`.

## WHY THE OBLIGATION HAS NO BODY FROM THE DELIVERED PIECES

This section is the reason the stop is final and not a delay. It is the
predecessor review's finding 3, which decides the GUARDED form, which is
the form this brief spells.

1. **The obligation is 765's telescope.** The brief says so: "The
   obligation is the same telescope, with `conv-at-Lδ` in place of the
   transport" (`LJ-1.766.md`, THE REASONING). The predecessor's signature
   is at `agents/tasks/LJ-1-765/Probe765.agda.txt:116-120`; the brief's is
   at `LJ-1.766.md:12-17`. The guards match: `IsOrd δ`, `⟨ δ ∈ˢ HS.M ⟩`,
   `⟨ Lset δ ∈ˢ HS.M ⟩` in front of the Sigma.

2. **The Sigma's third component reads at PINNED coordinates.** It is
   `⟨ (Lset δ ∷ δ ∷ z ∷ []) P652.⊨ₚ P667.matrix₃ ⟩` (`LJ-1.766.md:17`),
   and `matrix₃ = isOrd-at-p ∧̇ φ₃`
   (`agents/tasks/LJ-1-667/Probe667.agda:73`).

3. **The only assembly of that reading on record is `amb ∘ conv0`.** The
   predecessor's `mkWit` produces the exact triple this Sigma needs and its
   core is
   `amb δ ca cp ca≡Lδ cp≡δ a (conv0 ca cp a sat)`
   (`agents/tasks/LJ-1-765/Probe765.agda.txt:149-158`). The brief forbids
   the `amb` call (`LJ-1.766.md:19`), premise 1 records that `amb`
   heap-exhausts the cap ALONE at this caliber, 1454.50 s at peak RSS
   5247418368 B, EXIT 251 (`agents/tasks/LJ-1-765/lj-1.765-report.md:15-17`),
   and premise 5 records that the ascribed convert stays un-restored
   (`lj-1.765-report.md:23-24`).

4. **The non-transport supplier at pinned coordinates is measured
   uninhabited.** That supplier is what `[LJ-1.765-SPLIT]` attempted: its
   `conv-at-Lδ` is the Sigma's third component, "already at the grounded
   coordinates" (`agents/tasks/LJ-1-765-SPLIT/LJ-1.765-SPLIT.md:12-16`).
   The refusal is a statement about truth and not about cost: the floor
   with the designed hole elaborated clean at the heavy caliber, 4.45 s at
   peak RSS 904658944 B, EXIT 42 with the hole the only diagnostic
   (`agents/tasks/LJ-1-765-SPLIT/runs/floor765split.out:7-8,25`). The
   review's finding 3 closes the salvage for the guarded consumer: "The
   guarded form of the statement (guards restored) is true but is
   inhabited only by `amb ∘ conv0`"
   (`review-of-conv-at-Lδ.md:93-95`), because no hull code's value is
   definitionally `Lset δ` for a variable δ: `val` is inductive syntax
   (`src/L/Hull.lagda.md:88-91`) and `Lset` is a transfinite recursion
   (`src/L/Constructible.lagda.md:215-227`), so the equalities exist only
   propositionally inside the truncation `codeOf` delivers, and moving any
   reading along them is a subst on the `⊨ₚ` family, which is the measured
   wall (`review-of-conv-at-Lδ.md:97-109`).

5. **The obligation's own second hypothesis cannot supply the third
   component.** Its type consumes a reading and yields an equality:
   `⟨ (a ∷ p ∷ z ∷ []) ⊨ₚ matrix₃ ⟩ → IsOrd p → a ≡ Lset p`
   (`LJ-1.766.md:14`). An equality out is never a reading in. At
   `a := Lset δ`, `p := δ` it demands precisely the component the Sigma
   needs. This is readable off the signature; no construction turns it
   around.

The conclusion is the predecessor review's own: no inhabitant can be
assembled from the delivered pieces by type-checking alone, and a
construction that is not an assembly "would be new mathematics, priced by
the mathematician" (`review-of-conv-at-Lδ.md:139-146`).

## CORRECTED TARGETS, BESIDE THE ORIGINAL (D-10, dev/LESSONS.md:1375)

The original target was: the obligation at `LJ-1.766.md:12-17`, inhabited
with no `amb` call. The review lists two true variants; both move a
statement's type, so both are the mathematician's judgements:

- **T1, the Sigma reads at CODE coordinates.**
  `⟨ (fst (val ca) ∷ fst (val cp) ∷ z ∷ []) ⊨ₚ matrix₃ ⟩`, consuming
  `conv0` plus `hullClosed` with no transport. Every piece is measured
  green: `conv0` 10.41 s (`agents/tasks/LJ-1-764/lj-1.764-report.md:4-5`),
  the hull half 260.11 s
  (`agents/tasks/LJ-1-765/lj-1.765-report.md:110`), the frame 12.63 s
  (`lj-1.765-report.md:109`). The price is downstream: the soundness
  clause must be re-derived at code coordinates
  (`review-of-conv-at-Lδ.md:119-128`).
- **T2, restore the guards and re-cut the obligation at the site clause
  (iii) actually consumes**, with the witness carried
  (`review-of-conv-at-Lδ.md:129-137`). The review measures that T2 reduces
  to T1 or to new mathematics, because its non-transport half still needs
  a supplier at pinned coordinates.

## WHY NO PROBE AND NO RUN

- The stop clause (`LJ-1.766.md:21`) precedes the floor order (`:23`) and
  fired first.
- A floor prices a frame, not a truth. Both questions are already closed
  at this telescope: the composition floor with the body a hole
  heap-exhausted at `-M4g` at the 765 site, 1581.37 s at peak RSS
  4785717248 B (`agents/tasks/LJ-1-765/lj-1.765-report.md:112`), and the
  truth question is closed by `review-of-conv-at-Lδ.md`. Premise 1
  (`LJ-1.766.md:40`) forbids the retry, and rerunning the same shape for a
  different result is forbidden by the slot's own heap-wall clause.
- No Agda process started, so no heap wall was hit and the heap-wall
  clause has nothing to restructure. `Probe766.agda` is not written: a
  file that cannot typecheck rests at `.agda.txt`, never `.agda`
  (`LJ-1.766.md:25`), and a statement-plus-hole file with no run ordered
  adds no fact this review does not state.

## WHAT WOULD REOPEN THIS ROUTE

The predecessor's own condition, unchanged:
`review-of-conv-at-Lδ.md:139-146`. A supplier whose TYPE already reads at
`⟨ (Lset δ ∷ δ ∷ z ∷ []) ⊨ₚ matrix₃ ⟩`, built from Completeness or
elementarity without passing through code coordinates, or a cap ruling
above the wall `amb` measures. Both are owner or mathematician calls.
