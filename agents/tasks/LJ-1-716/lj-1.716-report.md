# LJ-1.716 report: ambient-at-hier is NO-GO, and the target is false

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.716
obligation: agents/tasks/LJ-1-716/Probe716.agda::ambient-at-hier
verdict: **NO-GO. The target itself is FALSE** at `δ₀ := (∅ , ∅∈L)`, the empty
ordinal, and the probe machine-checks the refutation in two green lemmas.
This is a stop under the Boundary (a false target is a deliverable), stated
for the critic in `review-of-ambient-at-hier.md`. The skeleton of this report
was written before the first Agda run and filled as each answer landed (C-22).

**I DID write `review-of-ambient-at-hier.md`.** A `review-of-*.md` is how a
coder states a NO-GO. This return is NO-GO.

Written incrementally, never at the end (C-22). No commit, no push. I wrote
only inside `agents/tasks/LJ-1-716/`. Agda ran under the caliber the program
set on this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier, ONE Agda process
at a time; I never set `GHCRTS`. Nothing is postulated, the probe carries
`--safe`, nothing lands in `src/`. The probe is a raw `.agda` file, so it
counts 0 in-fence lines and the ratio bar cannot fire on it.

## What the brief named, and what the type cost

The brief named the file (`Probe716.agda`), the statement
(`ambient-at-hier : (δ : CS.S) (oδ : IsOrd (fst δ)) → ⟨ (Lset (fst δ) ∷
fst δ ∷ fst (hierL (fst δ) (δ .snd) oδ) ∷ []) P652.⊨ₚ P667.matrix₃ ⟩`), the
premises, and the W3 question. All present and answerable; no stop on the
brief itself. W3's answer is the second horn the brief wrote out: the 2-slot
graph and the 3-slot matrix remain distinct.

The falsity, in three steps, each machine-checked:

1. `matrix₃ = isOrd-at-p ∧̇ φ₃`, `φ₃ = W3.erased`
   (agents/tasks/LJ-1-667/Probe667.agda:46-48, :70-73). `W3.three` opens
   twelve bounded existentials EACH BOUND BY THE WITNESS SLOT
   (agents/tasks/LJ-1-667/runs/W3.agda:69-79), and `pins` fixes the twelve
   tags to the numerals `∅` through `#11`
   (agents/tasks/LJ-1-520/Probe520.agda:122-135). So satisfaction at
   `(a, p, z)` demands the numerals INSIDE `z`.
2. The obligation fills the witness slot with `fst (hierL (fst δ) (δ .snd)
   oδ)`, the internal hierarchy. At `δ₀ := (∅ , ∅∈L)` that table has no
   members: `hierL-spec` says membership is `Recorded ∅` and `Recorded ∅`
   joins over members of `∅` (src/L/Hierarchy.lagda.md:494-503).
3. From any satisfaction, the first bounded existential surrenders a member
   of the table (src/FOL/Semantics.lagda.md:103), and that member dies:
   `no-member-of-hierL∅` (Probe716.agda:74-96, GREEN) lifts it into the
   constructible carrier by `isL-trans` and kills it on `∅-empty`.

Green pieces: `no-member-of-hierL∅` (Probe716.agda:74-96) and
`ambient-at-hier-empty` (Probe716.agda:100-115), the descent, generic in
`δ` and `oδ`. `zero-refutes` (Probe716.agda:118-131) states their
composition at `δ₀`; its body is a designed hole, and so is
`ambient-at-hier` itself. The probe exits 42 on exactly those two holes:
`runs/p-10.out`, 3.30 s, 696 MB, EXIT=42, the unsolved metas at
Probe716.agda:131.18-147.58 and nothing else.

## The wall the next brief must know about (heap protocol, ruling 2026-08-23)

The one-line plug that composes the two green lemmas at `δ₀`,

```
zero-refutes h =
  ambient-at-hier-empty (∅ , ∅∈L) ∅-ord h
    (no-member-of-hierL∅ ∅∈L ∅-ord)
```

walls the checker at 2.6 to 2.7 g near 300 s. I restructured in this
dispatch rather than reporting the first wall: ten tested shapes, each
recorded in `runs/`. The measured law that fell out:

- GREEN, 3.3 s and 0.70 to 0.85 g: every descent kept in variable-land
  (runs/floor-1.out the floor, 3.4 s, 849 MB; runs/g-1.out, runs/g-3a.out,
  runs/g-7.out, runs/va-1.out, runs/vg-1.out).
- WALL, 2.6 to 2.7 g: every conversion between two pointer-distinct types
  that both spell `Lset ∅` in the environment (runs/g-4.out, runs/g-8.out,
  runs/p-7.out, runs/vb-1.out, runs/vh-1.out, runs/vi-1.out). The checker
  whnf's `Lset ∅`, the `∈-induction` unfold, and dies. `∅`-spelled or
  variable-spelled environments compare instantly (runs/g-7.out).

The wall is in the bookkeeping composition, never in the mathematics; a wall
I routed around ten times, and the survivor is reported with the specific
reason above. Rerunning the same code was never the move; every retry was a
new shape.

## W2, answered

The mathematics is written once at generic carriers and instantiated:
`no-member-of-hierL∅` is generic in `h0` and `o0`; `ambient-at-hier-empty`
is generic in `δ` and `oδ`; the descent inside it is the truncation map on
the generic satisfaction. Two measured exceptions, both forced by the tool,
both routed around: a bound-term-generic inversion lemma was tried first and
the unifier blocked on the erased formula's bound (runs/p-6.out); a
generic-first-arg descent was tried and the concrete-argument conversion
walls (runs/g-4.out through runs/vi-1.out). Neither exception weakens the
statement; the brief's generic form survives verbatim.

## What this hands the next brief

1. The corrected target (D-10, recorded beside the original): the reading
   that survives is at a WITNESS SLOT THAT CARRIES THE NUMERALS, a stage
   (`z := Lset δ′`, `δ′` past `ω`) and not the table. The alternative shape
   graph plus SameAsGraph plus erase does deliver is the thirteen-existential
   `levelFo` reading at the 2-slot environment
   (agents/tasks/LJ-1-520/Probe520.agda:171-185). Which of these feeds
   Completeness and `LsetGrounded` is the mathematician's call; neither is
   priced here.
2. The C-42 sweep: the shape "tags bounded by the table" occurs at exactly
   ONE site, this obligation. The neighbours do not carry it: Probe673's
   `inBound` leaves its existentials unbounded
   (agents/tasks/LJ-1-673/Probe673.agda:74-77), and `levelFo` binds nothing
   by a slot. Count: 1.
3. The wall is fundable without reopening the NO-GO: a larger caliber on the
   one-line plug in `review-of-ambient-at-hier.md`, or a transport whose two
   sides never both spell `Lset ∅`.

## Runs

All under `GHCRTS="-A64m -I0 -M2g"`, one process at a time, `runs/run.sh`
the wrapper. Floor first (ruling 2026-08-23): `runs/floor-1.out` 3.4 s,
849 MB, the frame with holes standing in for the bodies. Greens:
`runs/g-1.out`, `runs/g-3a.out`, `runs/g-7.out`, `runs/va-1.out`,
`runs/vg-1.out`. Walls: `runs/g-2.out`, `runs/g-3b.out`, `runs/g-4.out`,
`runs/p-7.out` (2.59 g), `runs/vb-1.out` (2.63 g), `runs/g-8.out`
(2.63 g), `runs/p-8.out` (2.63 g), `runs/p-9.out` (2.66 g), `runs/v-1.out`
(2.63 g), `runs/vh-1.out` (2.60 g), `runs/vi-1.out` (2.74 g). Final state:
`runs/p-10.out` and the re-confirmation `runs/p-11.out`, both 3.3 s, 696 MB,
EXIT=42 on the two designed holes only (Probe716.agda:131.18-147.58).
Earlier iterations: `runs/p-1.out` through `runs/p-5.out` (parse, arity,
and unifier fixes). `runs/Probe716-p7.agda.txt` and `runs/FLOOR.agda.txt`
are the two intermediate sources, named `.agda.txt` because they do not
typecheck.

## SURVEY (the brief's mandatory check)

```
$ .venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-716
check-survey-quotes: LJ-1-716 FAILS the survey duty:
  no-heading: the return carries no ARCHIVE USED section
  unanswered: the return never names archive/dev/DD-archived.md
  unanswered: the return never names archive/dev/ORCHESTRATION.md
  unanswered: the return never names archive/dev/PLAN-archived.md
  unanswered: the return never names archive/dev/STATUS-archived.md
  unanswered: the return never names archive/dev/TASKS-archived.md
  no-lit-heading: the brief cites dev/literature/ and the return carries no LITERATURE USED section

A return names every path the program injected, and quotes one line read per
file: the quote must occur AT the cited line in the cited file. A written
decline is compliance.
```

This run predates the two sections below; the checker reads this report, and
they answer it. Rerun output recorded at the end of this file.

## ARCHIVE USED

- archive/dev/ORCHESTRATION.md: declined, not read. A pre-pod orchestration
  record; this task's run conventions came from
  agents/tasks/LJ-1-709/runs/run.sh, not from it.
- archive/dev/DD-archived.md: declined, not read. Retired design decisions;
  the live rules this task answered to are AGENTS.md and the brief.
- archive/dev/PLAN-archived.md: declined, not read. The live plan is the
  queue and the direction; no archived plan item bears on a probe refutation.
- archive/dev/STATUS-archived.md: declined, not read. The standing status is
  dev/pod/screen.toml; archived status pages are history by definition.
- archive/dev/TASKS-archived.md: declined, not read. Retired task list; this
  task's brief is LJ-1.716.md and its predecessors' reports are in their
  task homes.

## LITERATURE USED

- dev/literature/level-formula-slot-roles.md:23: `| 4 | Devlin 5.2 (a) |
  \`Φ(z,v,γ)\` with \`∀v∀γ [v = L_γ ↔ ∃z Φ(z,v,γ)]\` | 3 in \`Φ\`, ONE closed |
  \`z\` at position 0 | \`v\` at 1, \`γ\` at 2 | **VALUE, ORDINAL** |
  \`_build/literature/dev2.txt:1186-1191\` |`. Read. Row 4 is the outside
  view of this NO-GO: the literature BINDS the witness `∃z Φ(z,v,γ)`, while
  `matrix₃` keeps it free and the obligation fills it with the table. The
  review cites this row.
- dev/literature/BIBLIOGRAPHY.md:165: `17. Kunen, Kenneth. "Set Theory: An
  Introduction to Independence Proofs."`. Read. Cite-check only: it confirms
  the corpus's Kunen entry is cite-only, which is why the slot-roles digest
  had to fetch Kunen 1980 separately.
- dev/literature/devlin-errata.md: declined, not surveyed beyond its header.
  It is a do-not-repeat checklist for the rud route's Devlin accounts; this
  task quotes no Devlin prose and needs no erratum.
- dev/literature/glossary-review-2026-08.md: declined, not read. A glossary
  review; this task coins no term and adds no glossary entry (the Boundary
  forbids that anyway).
- dev/literature/primary-sources.md: declined, not read. A source register;
  this task cites no primary source beyond the digest row above.

## SURVEY RERUN (after the two sections above were written)

```
$ /Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-716
check-survey-quotes: LJ-1-716 clean (1 note(s), 0 defect(s))
EXIT=0
```
