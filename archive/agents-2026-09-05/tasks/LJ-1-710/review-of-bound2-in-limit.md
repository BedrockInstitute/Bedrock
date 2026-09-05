# Review of `bound2-in-limit`: NOT INHABITED

**Verdict: NO-GO, restated 2026-08-27 by the third dispatch on this task.** The
brief's term

    bound2-in-limit : <a limit that contains σ₁ and σ₂ contains
                       fst (bound2 σ₁ σ₂ o₁ o₂)>

is not inhabited by any return so far. The statement is not shown false. This
file states the stop with evidence that resolves today. Nothing lands in
`src/`, and `agents/tasks/LJ-1-710/Probe710.agda` carries the obligation only
as a well-formed, green typechecking statement.

## What closes green today

- The trimmed frame: `IsLimit` over `src/L/Ordinal` alone, carrying ordinality,
  successor closure and small-family union closure
  (`agents/tasks/LJ-1-710/Probe710.agda`, Section 1). Cold floor of the frame,
  `runs/t-small.out`: EXIT=0, 1.37 s, 278364160 bytes.
- The obligation, typed verbatim (`agents/tasks/LJ-1-710/Probe710.agda`,
  Section 2).
- The whole merge at an own-name family: `succFam` written out loud, then two
  clause compositions close membership, and `suc-ord` plus `setUnion-ord`
  give ordinality free (`agents/tasks/LJ-1-710/Probe710.agda`, Section 3). So
  every mathematical ingredient except one name is already proved.
- Re-run of the delivered file under the pane caliber on 2026-08-27:
  `runs/t-recap.out`, EXIT=0, 0.84 s warm, 275103744 bytes.

## The one wall, measured five ways, each site re-read today

The goal `⟨ fst (bound2 σ₁ σ₂ o₁ o₂) ∈ₛ α ⟩` reduces its head to
`⋃ (sett (Lift Bool) f)` for the where-bound family at
`src/L/Ordinal.lagda.md:190-191`. Consuming it through any union-closure
clause forces parity between that family and anything a probe can write.

1. Judgmental conversion by `refl`: dead,
   `agents/tasks/LJ-1-705/runs/p-26.out:5-8`.
2. Elaboration-time unification at the family argument: dead,
   `runs/t-e1.out:5-9`.
3. Qualified reference to the internal name `L.Ordinal.bound2.f`: no such
   symbol, `runs/t-paths2.out:5-8`.
4. A locally written twin convertible to itself: even `mf x` fails against its
   own case lambda at a variable position, `runs/t-selflambda.out:5-6`. The
   gap generalizes past `bound2`.
5. Constructor index-splitting: works everywhere it applies, which is how
   Section 3 closes; it cannot state the parity equation because the second
   side has no referable name.

An adversary review called this enumeration complete twice
(`review-of-LJ-1-710-1.md`, question 3; `review-of-LJ-1-710-2.md`,
question 3). No sixth strategy exists for a right side without a name.

## D-10: the target's truth

Not shown false. Classically the merge of two members below a limit ordinal
lies below it again; Devlin II.5 anchors the sequence reading
(`dev/literature/devlin-II5.md:221`). The OCR caveat on the classical corpus
(`dev/literature/primary-sources.md:23-24`) is recorded in the report, whose
load-bearing pages were re-extracted. The obstruction measured here is a
naming obstruction of the source tree, never a truth fact about the statement.

## What would reopen the route (src-side cure, minimal)

One line of new public surface in `src/L/Ordinal.lagda.md`:

- Name the merge family as a top-level definition and build `bound2` from it,
  or
- prove the limit-membership lemma directly in `src/`: from an ordinal,
  successor-closed, union-closed `α` and `⟨ σᵢ ∈ₛ α ⟩`, conclude
  `⟨ fst (bound2 σ₁ σ₂ o₁ o₂) ∈ₛ α ⟩`; Section 3 of the probe is the whole
  proof skeleton and needs only each member's successor supplied by the
  limit's own successor clause.

Until either exists, `[LJ-1.705]`'s split plan stays half paid: its first half
is proved here at an own-name presentation, its second half waits on that
surface.

## Why this task could not close before, and what this dispatch cured

Both adversarial rounds upheld the NO-GO, yet acceptance kept failing one
check: the judged report pair was fixed by `report_of()`
(`scripts/pod/check-survey-quotes.py:427`), and the report text never named
`dev/literature/primary-sources.md`, so conjunct 6 stayed red for every later
writer. The program ruled the citation belongs in the judged report,
`lj-1.710-report.md`, and is author-editable for exactly that. This
dispatch added the missing bullet there and corrected the three stale decimal
citations the reviews had filed; nothing else in the frozen records moved, and
no verdict above changed meaning.
