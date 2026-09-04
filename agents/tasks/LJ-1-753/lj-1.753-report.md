# LJ-1.753 report: bound-in-stage-from-mirror

## HEAD
head_slot: coder
machine: shared
agda_tier: wide

**Disposition: HEAP WALL, MEASURED AND LOCALIZED.** The obligation term is
WRITTEN COMPLETE in `agents/tasks/LJ-1-753/Probe753.agda.txt` (renamed
from `.agda` per the brief's naming rule: it cannot typecheck in any
admissible window). Every piece is built; nothing is postulated; no
holes. The type-check GROUNDS into a HEAP WALL: RSS 1.08 GB at t=0,
2.27 GB at t=5m (over the 2 GiB cap), 2.42 GB at t=15m; killed ~17m
with no completion (`runs/ground-snapshots.txt`,
`runs/probe753-ground.out`; two independent earlier runs
`runs/probe753-37.out`, `runs/probe753-40.out`). Four restructurings
were built and tested in this dispatch before this was reported (the
coder's wall clause). The critic's input is
`review-of-bound-in-stage-from-mirror.md`.

## The obligation and what the term does

`bound-in-stage-from-mirror` takes the brief's exact signature:
`StepKilledGen → (ca cp : Code) → fst (val cp) ≡ ∅ → fst (val ca) ≡
Lset ∅ → BoundInStage ca cp`, with the 673 `At` telescope as leading
arguments (in 673's own inner-module shape,
`agents/tasks/LJ-1-673/Probe673.agda:57-63`), and Amb7 imported beside
PT (the vendored green modules of 746-SPLIT-SPLIT). The construction:

1. The demand `⟨ [] ASt.AbsL.⊨ᵐ ∃̇ (mapFo val (inBound ca cp)) ⟩`
   quantifies over the restricted carrier `SL = Σ[ x ∈ S ] ⟨ x ∈ˢ
   Lset lam ⟩` (`src/FOL/Absoluteness.lagda.md:64-78`): three
   truncated existentials. The witnesses are the SL-pairs of `Lset ∅`,
   `∅`, and the twelfth numeral `n 12` (D-10,
   `agents/tasks/LJ-1-732/lj-1.732-report.md:126`); the frame's `∅∈λ`
   and `succλ` climb the numerals into `lam` and `Lset-mono` lifts each
   into `Lset lam` (`src/L/Constructible.lagda.md:365`).
2. The two `≐` conjuncts close by `sym` of the value hypotheses.
3. `matrix₃` is constant-free (`count-three = refl`,
   `agents/tasks/LJ-1-667/runs/W3.agda:84`), so the `mapFo val ∘
   mapFo slide` relabelling is INERT: conversion walks the tree, and
   no `countFo` enters the formula comparison.
4. The isOrd conjuncts and the 520-matrix rows (transitivity, the
   twelve pins, the domB kills, the implication whose `appAt`
   antecedent is bounded by `var 2 = n 0 = ∅` at
   `(v ∷ u ∷ n 0 ∷ γ15)`, the step-row kills) are re-spelled at the SL
   carrier from the green 732 rows (`Amb3`, `Amb5`, `Amb6`,
   `agents/tasks/LJ-1-732/runs/`), with every truncation elimination
   carrying an `Empty.isProp⊥*` motive. The appAt bound is verified at
   `src/L/Coding/Model.lagda.md:160-161`: `appAt f x y = ∃̇∈ (var f)
   (…)` with `f = suc (suc zero)`, so `lookup 2` of the implication's
   environment is `n 0 = ∅` and the antecedent dies at its own guard.

The `StepKilledGen` argument is consumed VACUOUSLY: the empty-instance
reading closes by the ∅-slot kills without it. This is a finding, not
an omission; see W3. The wall statement for the critic is
`review-of-bound-in-stage-from-mirror.md`.

## W3, the widest unmeasured term, ANSWERED WITH A MEASURED WALL

The brief asked whether BoundInStage at empty inhabits from the mirror
without `GraphAt` and without `AT.read`. The measured answer has three
parts:

1. **The inhabiting term EXISTS.** All the pieces listed above are
   built and the file parses. The isOrd, transK, pins, domB and
   step-row pieces each checked individually during the iterations
   (`runs/probe753-13.out` reached the graph rows; the later errors are
   strictly deeper).
2. **The full-term type-check GROUNDS.** Killed at 900 s
   (`runs/probe753-37.out`), re-killed at ~25 min
   (`runs/probe753-40.out`, `runs/prof5.out`), at 100 percent CPU.
3. **The wall is LOCALIZED by bisection.** With the domB-factor's
   antecedent-type dummied, the checker reaches the next position in
   **15.16 s** (`runs/bisect753b-1.out`): everything outside the
   domB-annotation is fast. The ground lives in the domB-annotation's
   antecedent-type, whose only nameable form contains the erased
   appAt-subformula `CntS.erase (∃̇∈ (var (suc (suc kk)))
   (appAt 2 1 0)) P` and its 21-deep count-proof chain
   (`W3.count-three` split 21 times, per the demand's own printed
   term in `runs/probe753-14.out`). The chain spelling was copied from
   the demand's printed term and corrected once (`l r l l r×17` for
   the A-factor, `l l r×16` for the B-factor, `runs/probe753-39/40`);
   the ground persists. This is the b7-3 phenomenon
   (`agents/tasks/LJ-1-746-SPLIT-SPLIT/runs/EraseIrr.agda:5-11`: the
   erase-spelling comparison normalizes the count terms) at a NEW site:
   the SL-carrier domB-row of the 520 matrix inside the 673 `At` hull
   telescope.

So: the wall is NEITHER `AT.read` NOR `GraphAt` — both are avoidable —
the wall is the **erase-spelling conversion of the erased appAt
subformula inside the domB-annotation at the restricted carrier**. The
next brief decides between: (a) fund an `erase-cong`-style transport at
this site (the EraseIrr cure, applied to the domB-annotation), or
(b) fund the meta-quirk workaround first (see below) and retry the
unannotated inline form.

## Restructurings tested before the wall was reported

1. Untyped where-names (`isOrd₁`, `domB`, …): Agda's where-meta
   unsolved-metas mis-solve against the Σ-splits of the reading
   (`runs/probe753-11.out`, `runs/probe753-14.out`).
2. Annotated where-names (ab/ba, transK): parses; the full check
   grounds (twice: `runs/probe753-39`, `runs/probe753-40`).
3. The chain spellings corrected to the demand's printed splits:
   still grounds.
4. The inline-λ approx (no where-names, no annotations — types taken
   from the demand directly): PARSES but only with `(λ`-glued form and
   exact continuation indents; the ascribed-ant variant walls in the
   parser (`runs/probe753-41.out` through `runs/probe753-54.out`).
   The last inline state is preserved in git-less form inside
   `runs/probe753-52.out`'s error print and the file was REVERTED to
   the deepest-checking state (2, the ab/ba version).

## Floor and price discipline

The floor ran before the proof (owner's ruling 2026-08-23): the
obligation's exact imports and signature with a holed body — 5.65 s
warm (`runs/floor753-3.out`), after a one-time 231.6 s cold-cone
warming of the 652/667/W3/520/673 interfaces this worktree had never
built (`runs/floor753-2.out`). ONE Agda process at a time, pane
caliber `-A64m -I0 -M2g` read and never set.

## Files

- `Probe753.agda.txt` — the complete grounding-term (renamed per the
  brief's rule; a `.agda` file that cannot typecheck in-window would
  poison every later build).
- `runs/Floor753.agda.txt`, `runs/floor753-*.out` — the floor.
- `runs/Bisect753.agda.txt`, `runs/Bisect753b.agda.txt`,
  `runs/bisect*.out` — the localization.
- `runs/probe753-*.out` — every iteration.

## W2 answer

Honored by reuse: BoundInStage, Code, val, inBound are 673's; the
numerals, kills and pin-shapes are 732's Num/Amb3/Amb5/Amb6 content
re-spelled at the restricted carrier (an instantiation, not a second
statement); Amb7/PT are the brief-ordered imports. Nothing is
duplicated that the tree already states.

## Ratio bar

The deliverable is a raw `.agda.txt` probe: no ` ```agda ` fence, 0
in-fence lines. The bar cannot fire.

## Mandated paste

    $ .venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-753
    check-survey-quotes: LJ-1-753 clean (0 note(s), 0 defect(s))

    exit 0. (The worktree carries no .venv; the main tree's interpreter
    ran the script against THIS worktree, as in the 744-SPLIT return.)

## ARCHIVE USED

- archive/dev/DD-archived.md: declined, not read. The vendor- and
  transport-cures this task cites come from the predecessor's live
  reports at their own sites.
- archive/dev/ORCHESTRATION.md: declined, not read. The loop
  operation is fixed by the standing files.
- archive/dev/PLAN-archived.md: declined, not read. No plan-level
  question arose.
- archive/dev/TASKS-archived.md: declined, not read. Closed task
  history is not evidence for an elaboration wall.
- archive/dev/STATUS-archived.md: declined, not read. The screen is
  the only standing status.

## LITERATURE USED

- dev/literature/devlin-errata.md: declined, not read. No Devlin
  citation is under test; the mathematics is the tree's own empty
  instance.
- dev/literature/glossary-review-2026-08.md: declined, not read. No
  translation term was chosen.
- dev/literature/level-formula-slot-roles.md: declined, not read. The
  slot roles are fixed by the imported modules.
- dev/literature/formalizations-landscape.md: declined, not read. No
  formalization-comparison is in play.
- dev/literature/BIBLIOGRAPHY.md: declined, not read. No source is
  quoted.
