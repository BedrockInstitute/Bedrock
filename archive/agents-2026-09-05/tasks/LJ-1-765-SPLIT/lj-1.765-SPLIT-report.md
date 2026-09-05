# LJ-1.765-SPLIT report: conv-at-Lδ, the conversion at the grounded coordinates

## HEAD

head_slot: coder
machine: shared
agda_tier: heavy
task: LJ-1.765-SPLIT
obligation: agents/tasks/LJ-1-765-SPLIT/Probe765Split.agda::conv-at-Lδ
verdict: **NO-GO, AND IT IS NOT A RESOURCE WALL.** The obligation's
type, as the brief spells it, is UNINHABITED at its own generality:
`matrix₃ = isOrd-at-p ∧̇ φ₃` (Probe667.agda:73), and `isOrd-at-p`
(Probe667.agda:59-66) reads the parameter slot, which the obligation
binds to the bare variable `δ : S` with no `IsOrd δ` in the
telescope. The predecessor kept that guard in exactly that position
(Probe765.agda.txt:118). The second failure is the witness slot:
`φ₃` bounds its twelve tags by `z`, and the obligation's `z := fst a`
is an arbitrary stage element. A third finding closes the salvage:
for variable `δ`, no hull code's value is definitionally `Lset δ`
(src/L/Hull.lagda.md:72-91), so ANY pinning of the coordinates costs
a subst along the `⊨ₚ` family, which is the measured wall `amb`
(lj-1.765-report.md:16). The route this split names has no
inhabitant; the corrected targets are in the review, and they move a
statement's type, which is a mathematical judgement. No heap wall was
hit anywhere in this dispatch: the heaviest run is the warm-up of
Probe667 at 1955577856 B against the 4 GB cap
(runs/warm-p667.out:7), and the floor itself peaked at 904658944 B
(runs/floor765split.out:8). The review is written:
review-of-conv-at-Lδ.md. The probe rests at `.agda.txt` (designed
hole), never `.agda`. Nothing in `src/` is touched.

Written incrementally from the first minutes (C-22). No commit, no
push. Only this task directory is touched.

## THE DELIVERABLE

- `Probe765Split.agda.txt` -- the obligation's statement, the brief's
  signature verbatim, with the body a DESIGNED HOLE. Imports trimmed
  to what the statement's own rows name (P652, P667): no P673, no
  P692, no vendored interfaces, because `conv0`, `Convert`, `inBound`
  and the hull half appear in no row.
- `review-of-conv-at-Lδ.md` -- the NO-GO, with the corrected targets
  beside the original (D-10). This file is the deliverable the
  brief's `no-go-stated` branch reads.
- `runs/run.sh` -- the run instrument: one Agda process per
  invocation, the caliber read from the pane and never set, 1800 s
  `timeout` wrapped inside `/usr/bin/time -l`.
- `runs/*.out` -- every run record this report cites.

## THE RUNS

ONE Agda process at a time, sequential, never two; `GHCRTS` was read
from the pane at every run and never set; every `.out` line 1 shows
`-A64m -I0 -M4g`, the heavy caliber. This worktree's import cone was
cold, so it was warmed bottom-up first, each module its own process.

| run | file | rc | wall | peak RSS | evidence |
|---|---|---|---|---|---|
| warm Probe652 | `agents/tasks/LJ-1-652/Probe652.agda` | 0 | 4.94 s | 900710400 B | runs/warm-p652.out:1,5,6,23 |
| warm Probe667 | `agents/tasks/LJ-1-667/Probe667.agda` | 0 | 12.71 s | 1955577856 B | runs/warm-p667.out:1,6,7,24 |
| **FLOOR** | `Probe765Split.agda` (temp same-stem copy, deleted after) | **42, designed** | **4.45 s** | **904658944 B** | runs/floor765split.out:1,7,8,25 |

Floor discipline: the statement's body is a hole by design, so this
one run is both the 2026-08-23 floor and the whole probe: there is no
harder part behind the hole to price. The run's only diagnostics are
the designed hole's unsolved meta (`UnsolvedInteractionMetas` at
66.20-21, the body row only, runs/floor765split.out:4-7): no type
error, no unsolved constraint. The type ELABORATES: the frame carries
it at the heavy caliber at 4.45 s, BELOW the warm-up cost of its own
imports, with no wall anywhere near, so the obstruction is truth and
not cost, which is the distinction the brief's NO-GO classes turn on
("Do not write a `review-of` for a resource wall").
The temp `.agda` copy was removed after its run; the tracked
instrument stays `.agda.txt`, and no file that cannot typecheck rests
at a `.agda` path.

## WHY THE TYPE IS UNINHABITED (summary; full detail and cites in the review)

1. `matrix₃ = isOrd-at-p ∧̇ φ₃` (Probe667.agda:73). `isOrd-at-p`
   (Probe667.agda:59-66) is the tree's ordinality matrix at slot 1,
   the same two conjuncts as `isOrdAt`
   (src/L/BoundedSubset.lagda.md:795-798), and the tree carries the
   extraction `isOrdAt-out : ⟨ (x ∷ []) ⊨ₚ isOrdAt ⟩ → IsOrd x`
   green (src/L/BoundedSubset.lagda.md:813). The obligation binds
   slot 1 to bare `δ : S`. An inhabitant at δ := ⁅ sucV ∅ ⁆s (the
   singleton former `⁅_⁆s` and `sucV` are tree-named,
   src/V/Coding.lagda.md:52) would put `IsOrd ⁅ sucV ∅ ⁆s` in reach,
   and that set is not transitive: `sucV N = N ∪ ⁅ N ⁆s`
   (cubical Constructions.agda:160-161), so `sucV ∅` has the member
   `∅` while `⁅ sucV ∅ ⁆s` does not.
2. `φ₃` is `W3.erased`: the twelve tags are bounded by the witness
   slot z, outermost bound `∃̇∈ (var 2)` (W3.agda:26-28, 56-59, 75),
   and the reading of `∃̇∈` is a join over the bound's members
   (src/FOL/Semantics.lagda.md:103). At `z := fst a` for an `a` whose
   value lacks the tags, the join is empty. In
   `grounded-from-complete` z is NOT arbitrary: it arrives from
   `hullClosed` carrying `SatIn` (Probe765.agda.txt:149-158); the
   brief's signature drops that carrier.
3. The salvage is closed: for variable δ, no code value reduces to
   `Lset δ`. `Code` is inductive syntax, `val (base m) = emb m`,
   `val (wit k ψ cs) = Sum.rec (search ...) (λ _ → junk)``
   (src/L/Hull.lagda.md:72-91); `Lset` is a transfinite recursion
   (src/L/Constructible.lagda.md:215-227). So pinning the reading to
   `(Lset δ, δ)` always costs a subst on the `⊨ₚ` family, and that
   primitive is the measured wall `amb`, 1454.50 s at peak 5.25 GB
   ALONE at `-M4g` (lj-1.765-report.md:16).

## WHAT THE NEXT BRIEF NEEDS

The zero-transport variants all move a pinned coordinate out of a
statement's TYPE; none of them is a term this slot can write without
a new ruling. The review lists them in the order they cost least:
(1) a `grounded-from-complete` whose Sigma reads at the CODE
coordinates `(fst (val ca) ∷ fst (val cp) ∷ z ∷ [])`, consuming
`conv0` + `hullClosed` with NO transport (every piece of that
assembly is measured green); (2) the guards restored
(`IsOrd δ`, and the witness carried) with the obligation re-cut at
the site clause (iii) actually consumes. Both change a statement's
type: mathematician's judgement, not mine.

## W2 ANSWER

Honored by non-writing. This dispatch wrote no lemma, no duplicate of
any generic statement, and no new mathematics: the probe carries the
obligation's own signature and a hole, and every fact it reports is
read from files already in the tree. The generic carriers
(`hull-convert`, `convert-generic`, `isOrdAt-out`) are consumed as
citations, never restated.

## W3 ANSWER

**NO.** A conversion at `(Lset δ, δ)` does not check, and not for
cost: the brief's exact type is uninhabited (findings 1 and 2), and
the guarded form is uninhabited without the transport the brief
forbids (finding 3). The floor run shows the type elaborates clean at
the heavy caliber, so this NO-GO is a statement about the
mathematics, and the review is where it is stated.

## SURVEY CHECK

Ran before return, as ordered. This worktree has no `.venv` of its
own; the pinned interpreter of the main checkout ran the gate:

```text
$ /Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-765-SPLIT
check-survey-quotes: LJ-1-765-SPLIT clean (0 note(s), 0 defect(s))
```

## ARCHIVE USED

- archive/dev/DD-archived.md:22 - read; it is the rule my W2 answer
  reports against: "MAXIMUM REUSE is the architecture's objective,
  and it is the same rule as WRITE IT GENERIC." The dispatch
  consumed generic carriers as citations (isOrdAt-out,
  hull-convert, convert-generic) and restated none of them.
- archive/dev/ORCHESTRATION.md - declined, not read. The clauses that
  bind this dispatch are in the brief, the slot file and AGENTS.md.
- archive/dev/PLAN-archived.md - declined, not read. No plan-level
  question arose; the finding is local to one statement's truth.
- archive/dev/TASKS-archived.md - declined, not read. The
  predecessors this task needs (764, 765) are named in its own brief
  and read from the live tree.
- archive/dev/STATUS-archived.md - declined, not read. Standing
  status is `dev/pod/screen.toml` alone.

## LITERATURE USED

- dev/literature/glossary-review-2026-08.md - declined, not read.
  This dispatch coins no term.
- dev/literature/primary-sources.md - declined, not read. No
  mathematical prose was written or checked.
- dev/literature/level-formula-slot-roles.md - declined, not read.
  The slot roles this task needed are cited from the code and its
  comments (Probe667.agda:70-73), not from the note.
- dev/literature/BIBLIOGRAPHY.md - declined, not read. No source
  question arose.
- dev/literature/devlin-errata.md - declined, not read. No Devlin
  text is judged; the refutation is internal to the tree's
  semantics.
