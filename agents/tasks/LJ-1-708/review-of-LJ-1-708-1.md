# Review of LJ-1.708#1: the door-free NO-GO, attacked

## HEAD
head_slot: coder
machine: shared
task: LJ-1.708
obligation: agents/tasks/LJ-1-708/Probe708.agda::below-direct
reviewed: agents/tasks/LJ-1-708/lj-1.708-report.md, its stated NO-GO
agents/tasks/LJ-1-708/review-of-below-direct.md, and the probe
verdict: **upheld**

## THE LENS I ATTACKED WITH

DD25's four questions, read at their archived home today
(`archive/dev/DD-archived.md:35`): is the refusal correct on its own
numbers; is the measurement sound; did the BRIEF cause the outcome;
and is there a cure the return missed. Section 6.6's live list is the
three questions answered below. The pointer this brief carries for
them (`dev/memos/LJ-4-pod-program-design.md:2853-2858`) has drifted:
the memo moved and the list now lives at
`dev/memos/LJ-4-pod-program-design.md:3062-3065`, section 6.6 opening
at :3023. The pointer is program-written and was not authored by the
predecessor, so it costs no defect.

## THE CHANNEL FACTS THIS INSTANCE RAN ON

`dev/pod/transitions/2026-08.jsonl` in this isolated worktree carries
4617 sequences and ends before this task: its last line is LJ-1.692 to
RUNNING at 2026-08-26T23:09Z, and NO line in it carries
`"task": "LJ-1.708"`. So every run fact here comes from the acceptance
arm, which the brief says is written into this checkout:
`runs/accept-1.out` records caliber `-A64m -I0 -M2g`, tier wide,
concurrency 2, agda slot `Probe708.agda` rc 0 in 3.23 s, 17 changed
files all own, obligations delta 0, obligations open 1, conjuncts 1 to
5 held and conjunct 6 FAILED, error_class lint, exit 1. The `.pod`
stamp reads pod=1, heads=665f7468, at=2026-08-27T04:01:36Z.

One naming fact, so no later reader stumbles: the task home holds
`review-LJ-1-708-1.md`, which is the PROGRAM'S OWN review brief, not a
leftover return. Section 6.6 (memo :3059-3060 and 3067-3069) fixes the
pair: the input brief is `review-<PRED>.md`, the reviewer's output is
`review-of-<PRED>.md`, deliberately different names. Nothing here
deletes or edits it.

## WHY THIS ESCALATED, AND HOW IT IS FIXED

Attempt 1 returned a real result and failed acceptance conjunct 6 on
the survey duty. The checker the gate runs judges the task's OWN
return against the task's WORK brief (check-survey-quotes resolves
brief and report from the task directory; precedent: the LJ-1.685 and
LJ-1.624 cycles parked on sys-lint-accept until the task report itself
carried the survey sections, which is the cure those cycles applied).
So this dispatch does TWO things and says both:

1. writes this review; and
2. appends the missing `## ARCHIVE USED` and `## LITERATURE USED`
   sections to `agents/tasks/LJ-1-708/lj-1.708-report.md`, answering
   the five archive candidates and five literature candidates THAT
   BRIEF injected (its block names `archive/dev/STATUS-archived.md`
   and `archive/dev/TASKS-archived.md`; this dispatch's own review
   brief drew a different sample, naming
   `archive/dev/measurements/README.md` and `archive/dev/README.md`).
   Both files were skimmed at header level and declined in writing;
   nothing about them is quoted as evidence.

After writing, the pre-commit set was re-run by hand and the gate pair
went clean. `check-survey-quotes.py LJ-1.708` now exits 0, and the
explicit review pair (`--brief agents/tasks/LJ-1-708/review-LJ-1-708-1.md
--report agents/tasks/LJ-1-708/review-of-LJ-1-708-1.md`) also exits 0.
No other tree state was touched beyond these two task-home files, both
inside `agents/tasks/LJ-1-708/`.

## QUESTION 1. DOES THE VERDICT LINE MATCH ITS OWN BODY?

YES, in both documents the predecessor wrote.

The report HEAD states 「NO-GO on the closed term from the licensed
triple; GO on the delivered record」and names
`review-of-below-direct.md` as the stated NO-GO
(`agents/tasks/LJ-1-708/lj-1.708-report.md:7-13`). The body delivers
exactly that split: section 4 reports the attempt stopped at three
unsolved metas, section 3 prices the floor, section 8 tables the runs,
section 11 hands the residue forward. The companion
(`agents/tasks/LJ-1-708/review-of-below-direct.md:8-11`) states the
same structural reason: no row among the triple concludes a stage
membership except FROM another stage membership or a carrier
membership, so every assembly bottoms out below any licensed rule.

I re-derived the headline numbers from the run files rather than
trusting the tables. All match:

- `runs/cand-2.out:6-8` lists exactly three unsolved metas, at
  `cand-1.agda` 71.44-45, 71.47-48 and 71.49-50. Column by column these
  are the three undersupplied slots of
  `Lset-mono {α = W3.step 3 (fst δ)} {β = _} _ _` at
  `runs/cand-1.agda.txt:71`: the beta index, the beta-membership
  premise, the base membership. The predecessor's reading is the only
  one the columns allow.
- `runs/floor-2.out` shows the designed hole
  ([UnsolvedInteractionMetas] at FLOOR.agda:52.23-59), 3.46 s real,
  peak 729,366,528 bytes, EXIT=42, matching section 3's numbers and
  `runs/FLOOR.agda.txt:52`, where the hole sits under the obligation
  type typed at :51.
- `runs/p-2.out` EXIT=0 in 3.59 s; rechecks 2.98, 3.14, 3.23 s, median
  3.14 s; `runs/final-1.out` EXIT=0; `runs/meter-obligation.out` reads
  `missing exit=42 3.27s ...::below-direct ([NotInScope])` and
  `witness: 1 UNRESOLVED of 1, 3.27 s, probe_red=False`.
- Arithmetic held: raw totals 84 + 52 + 71 = 207 lines across probe,
  floor and attempt; the code counts reproduce exactly under the
  stated awk recipe, 28, 30 and 31; peaks are 45, 34 and 33 percent of
  the 2,147,483,648-byte wide cap. No heap event appears in any `.out`.

One mismatch inside tolerance: the report cites the meta rows as
`runs/cand-2.out:4-8`, the companion as :6-8. Both describe the same
three errors; :4 is the [UnsolvedMetaVariables] banner above them.
Neither span is false.

## QUESTION 2. IS EVERY LOAD-BEARING CLAIM BACKED BY A file:line THAT RESOLVES TODAY?

YES. Every citation I tested resolves and says what the return claims.
The load-bearing ones:

- Premise 1's basis, `agents/tasks/LJ-1-679/review-of-LJ-1-679-1.md:154-157`,
  really records 「ingredients ... `Lset-out` ... and `Lset-mono` ...
  They do not assemble it」, and the corrected attempt named at
  :229-233. Resolves.
- `agents/tasks/LJ-1-697/lj-1.697-report.md:9-10` states NO-GO on the
  closed term and GO on W3 plus the assembly; :110 names
  `ord∈Lset→∈` the specialised out-lemma. Resolves.
- `src/L/Ordinal/Stages.lagda.md:265-268`: the lemma exists, concludes
  plain `⟨ x ∈ˢ α ⟩`. Resolves.
- `agents/tasks/LJ-1-697/Probe697.agda:72-74` is the target type, and
  `agents/tasks/LJ-1-708/Probe708.agda:69-71` reproduces it token for
  token modulo the `W3.` module alias; `:81-86` is the green
  `from-below` assembly. Both resolve.
- Producer rows: `src/L/Constructible.lagda.md:301-304` (`𝒟ₒ-intro`),
  :329 (`Lset-in` carries a `𝒟ₒ` premise), :365-366 (`Lset-mono`,
  extends never starts);
  `agents/tasks/LJ-1-697/runs/W3.agda:42-44` (`Lset∈suc` fires
  `𝒟ₒ-intro` at :44); :55-62 (`climb`, `ordinal-in`, taken via the
  using-list at `Probe708.agda:65-66`);
  `src/L/Stage.lagda.md:188` (`stage-mem` places at its own earliest
  stage); `src/L/StageBound.lagda.md:122` (collection-data family,
  out of license). All resolve.
- The frame is `[LJ-1.679]`'s verbatim: `Probe679.agda:63-67` equals
  `Probe708.agda:56-60`, telescope for telescope, so premise 5's
  「known good AT this frame」is honest.
- `[LJ-1.707]`'s GO as an assembly,
  `agents/tasks/LJ-1-707/lj-1.707-report.md:9-10`, and the bound
  hypothesis named at `agents/tasks/LJ-1-707/Probe707.agda:60-63`.
  Both resolve.
- Law anchors resolve: D-10 at `dev/LESSONS.md:1375`, D-26 at :1735,
  C-22 at :2307, P-l at :2367, C-42 at :3762.

Two soft spots, neither authored by the predecessor and neither
load-bearing. First, the W3 estimate 「90 to 220 lines」cites
`review-of-LJ-1-679-1.md:154`, but that line holds the two-lemma
finding, no figure; the number was inherited verbatim from the work
brief's own W3 paragraph (`LJ-1.708.md`, W3). The delivered price sits
in the band anyway and the real price is counted directly, so nothing
rests on it. Second, the drifted memo pointer named under my lens
above. Record both so the next brief builder trims them.

## QUESTION 3. IS THE ENUMERATION COMPLETE?

ALMOST. The verdict survives a completed enumeration, but the
companion's boundary claim 「No sixth producer exists for
⟨ t ∈ˢ Lset w ⟩ shapes」(`review-of-below-direct.md:57-58`) is not
true literally. A sweep of `src/` for conclusions of that shape finds
at least three rows the census does not list:

1. `src/L/Ordinal/Stages.lagda.md:434`, `ord∈Lset-suc :
   ⟨ α ∈ˢ Lset (sucV α) ⟩` for IsOrd α. Its proof runs through
   ∈-induction and `𝒟ₒ→Lset-suc`, so it belongs to the door family,
   and it places ORDINALS only; the table element is not an ordinal in
   general. It closes none of the three metas.
2. `src/L/Choice/Step.lagda.md:159`, `birth-mem`, derived from census
   row `stage-mem` plus `birth-suc`, carrying an `⟨ isL x ⟩` premise.
   Derivative of a counted row; closes nothing new.
3. `src/L/BoundedSubset.lagda.md:1212`, `∅∈Lset1`, proved from
   `∅∈𝒟ₒ` alone. Constant left side, door family; cannot place the
   table.

Each miss is either derivative of a counted producer, constant, or
door-family, and NONE stands in the licensed triple, whose boundary is
fixed by the brief and by the using-list itself. So the STRUCTURAL
finding stands: the triple lacks any base producer able to place
`fst (hierL (fst δ) (δ .snd) oδ)` fresh, the three metas of
`runs/cand-2.out:6-8` are exactly the unproducible slots, and the
NO-GO on the closed term is correct. The downstream bills stand
unchanged: fund `[LJ-1.704]`'s identification keystone and
`[LJ-1.707]`'s bound hypothesis; the door-free ambition needs a NEW
producer funded as its own task, priced against the CORRECTED census.

There is no cure the return missed inside its license, and the brief,
by fixing the toolkit to three rows, caused no false negative: the
attempt went as far as the license allows, one rule, three empty
slots, counted. The floor ran BEFORE the proof attempt and imports
were trimmed (the frame costs 3.46 s and 0.73 GB), the heap-wall clause
never fired, and no failing shape was rerun unchanged: `floor-1` to
`floor-2`, `cand-1` to `cand-2`, `p-1` to `p-2` are each a shape
change, and the plumbing rows are named as such. Measurement sound,
refusal correct on its own numbers.

## UPHELD, WITH ONE CORRECTION TO RECORD

Upheld. The task should close on the stated NO-GO. Record beside it:
the producer census of `review-of-below-direct.md` section 3 gains the
three rows listed under question 3, and its completeness sentence must
be read as 「no sixth DOOR-FREE PRODUCER ABLE TO PLACE THE TABLE」,
which is what was actually measured.

## ARCHIVE USED

Corpus searched over archive corpora at this checkout. Per candidate:

- `archive/dev/DD-archived.md` read at :35 for the reviewer lens only:
  "The questions are: is the refusal correct on its own numbers; is
  the measurement sound; did the BRIEF cause the outcome; and is there
  a cure the return missed." Line 35 in full, where I confirmed it.
- `archive/dev/ORCHESTRATION.md` not surveyed: the retired
  orchestrator's operating rules; dispatch routing is not at issue in
  an Agda toolkit attack, and routing facts came from the accept arm
  and scripts. Declined.
- `archive/dev/PLAN-archived.md` not read: retired planning record,
  its header points to the live screen it was replaced by; bears
  nothing on this probe. Declined.
- `archive/dev/STATUS-archived.md` not read: retired goal table of the
  old internalization route, superseded by `dev/pod/screen.toml`;
  bears nothing on this probe. Declined.
- `archive/dev/TASKS-archived.md` not read: retired L3.32-T series
  index, no bearing on this task home. Declined.
- `archive/dev/measurements/README.md` not used: describes the format
  of archived timing records; this review takes its run facts from
  this task's own `runs/` directory, which is live. Declined.
- `archive/dev/README.md` not used: a directory-level description of
  the retired developer records; no claim of this review rests on it.
  Declined.

## LITERATURE USED

Corpus searched over dev/literature at this checkout. Per candidate:

- `dev/literature/BIBLIOGRAPHY.md` not surveyed: the retired rud
  route's source list; this attack cites only this tree's own proofs
  and probes. Declined.
- `dev/literature/devlin-errata.md` not used: documented error classes
  for the book account; the measured gap here is tree-side lemma
  supply, not a book account. Declined.
- `dev/literature/primary-sources.md` not used: second fetch round of
  the retired route; no bearing on the producer census. Declined.
- `dev/literature/level-formula-slot-roles.md` not surveyed: how each
  author states levelhood, useful for prose phase planning; nothing in
  this NO-GO turns on the level formula. Declined.
- `dev/literature/glossary-review-2026-08.md` not used: a glossary
  protocol deliverable; no translation term is at issue here.
  Declined.
