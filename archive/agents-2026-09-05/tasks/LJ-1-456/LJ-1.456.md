# LJ-1.456: the counting leg end to end, against the landed chapter

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-456/Probe456.agda`:

    bounded-from-residue : Residue → ⟨ x ∈ˢ Lset κ ⟩

where `Residue` is `[LJ-1.447]`'s hypothesis, restated at its delivered type,
and the body composes `[LJ-1.452]`'s `sq-data-closed` with the LANDED
`bounded-from-trunc` (`src/L/StageBound.lagda.md:109-110`). **It proves no new
mathematics. It shows, in one file, that the counting leg's whole remaining
bill is `Residue`.** Land nothing in `src/`.

**READ TWO REPORTS BEFORE ANY AGDA, AND STOP IF EITHER VERDICT IS NOT `GO`.**
`agents/tasks/LJ-1-452/lj-1.452-report.md` (`:75`, committed at `7ee150a`) and
`agents/tasks/LJ-1-447/lj-1.447-report.md` (`:53`, committed at `ef44a34`).
**Take both types from the probes that typechecked, never from a brief.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-456/Probe456.agda::bounded-from-residue"]

## SCOPE (write)
- agents/tasks/LJ-1-456/Probe456.agda
- agents/tasks/LJ-1-456/lj-1.456-report.md
- agents/tasks/LJ-1-456/review-of-bounded-from-residue.md
- agents/tasks/LJ-1-456/runs/

## PREMISES

1. `[LJ-1.452]` is GO on `sq-data-closed`, the square law as DATA over the band under one hypothesis. Basis: agents/tasks/LJ-1-452/lj-1.452-report.md:75
2. Its delivered term is at the probe that typechecked. Basis: agents/tasks/LJ-1-452/Probe452.agda:92
3. Its report states that the adapter to the landed `SqFam` is the IDENTITY. Basis: agents/tasks/LJ-1-452/lj-1.452-report.md:87
4. `[LJ-1.447]` is GO on `descent-both`, which carries `Residue` as its one hypothesis. Basis: agents/tasks/LJ-1-447/lj-1.447-report.md:53
5. The consumer is LANDED and takes a truncated family. Basis: src/L/StageBound.lagda.md:109
6. `SqFam` is landed beside it. Basis: src/L/StageBound.lagda.md:35
7. `SqCollect` is landed too, and it is the TRUNCATED route's residue, which this task does not use. Basis: src/L/StageBound.lagda.md:43
8. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
9. The architecture is a CANDIDATE and only a measurement settles it. Basis: dev/pod/screen.toml:10
10. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**EVERY LINK EXISTS AND NO FILE HOLDS THE CHAIN.** `[LJ-1.452]` gives `sq δ` as
DATA at every band ordinal under `Residue`. `src/L/StageBound.lagda.md:109` takes
`∥ SqFam α ∥₁` to the bounded-subset conclusion, and it is in `src/`. The step
between them is `∣_∣₁`, and `[LJ-1.452]`'s report says the adapter is the
identity.

## WHAT IS MISSING

The composition, and the sentence it makes checkable: **the counting leg's whole
remaining bill is one statement about two ordinals.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** Quote `sq-data-closed`'s type
(`Probe452.agda:92-96`) and the landed `SqFam` (`src/L/StageBound.lagda.md:35-41`)
side by side. `[LJ-1.452]` reports the adapter as the identity. **Verify that
yourself and say so.** A predecessor's claim about an adapter is a claim, and
this file is where it becomes a term.

**THE SHAPE.** Import `L.StageBound` from `src/`. Take `sq-data-closed` and
`Residue` as module hypotheses at their delivered types. Apply the adapter, then
`∣_∣₁`, then `bounded-from-trunc`. **Import no probe.**

**DO NOT REBUILD `[LJ-1.452]`'s RECURSION AND DO NOT REBUILD EITHER SEAL.** This
file holds no `κL`, no `κC` and no induction.

**DO NOT INHABIT `Residue` AND DO NOT POSTULATE IT.** Nothing in this tree
proves it and nothing refutes it.

**REQUIRED REPORT SECTION `## WHAT IS LEFT`.** State `Residue` as a type, say in
one sentence what it says in words, and say which of the two routes to the same
conclusion it belongs to: the DATA route here, or the TRUNCATED route whose
residue `SqCollect` is already landed at `src/L/StageBound.lagda.md:43`.
**Do not rank the two. That ranking is `[LJ-2.5]`'s.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 80 lines in the probe, of which the obligation is
about 12. BASIS: `agents/tasks/LJ-1-420/Probe420.agda` is 99 lines for an
assembly of this class and its whole term is three lines under a stated
telescope. Comparables are of SHAPE.

## W3, THE WIDEST UNMEASURED TERM

It is the adapter, because a predecessor reported it and no file has run it.

    adapter : ((δ : V ℓ) → ⟨ δ ∈ sucV α ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → sq δ)
            → SqFam α

**Write it as the identity, typecheck it ALONE with the obligation omitted, and
report the result.** One side quantifies `(δ : V ℓ)` with `∈`, the landed side
quantifies `(δ : S)` with `∈ˢ`. If it is not the identity, the elaborator's
error at `file:line` IS the finding and it outranks the obligation.

ESTIMATE for W3: three lines and under 5 seconds on top of the chapter import.

Report the median wall time and peak RSS over three forced rechecks.

## WHAT GO AND NO-GO EACH EARN

**A GO GIVES `[LJ-2.5]` ONE TYPE.** It says the bounded-subset lemma's
conclusion follows from `Residue` alone, against a chapter that is in `src/`.

**A NO-GO SAYS THE ADAPTER IS NOT THE IDENTITY**, which would mean a delivered
report over-claimed, and that is worth finding.

## BRANCHES
```toml pod-branches
[[branch]]
id = "go"
priority = 10
action = "done"
outcome = "go"

  [branch.when]
  exit_code = 0
  obligations_delta_max = -1
  heap_wall = false

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-456/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-456-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-456/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-456/Probe456.agda"]
  changed_files_none = ["agents/tasks/LJ-1-456/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-456/review-of-*.md"]

[[branch]]
id = "heap-wall-escalate"
priority = 30
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  heap_wall = true

[[branch]]
id = "ran-long-and-changed-little"
priority = 50
action = "park"

  [branch.when]
  seconds_min = 3600.0
  changed_files_count_max = 1
```

## YOUR ROLE (program-generated, do not edit)

**You write the Agda this brief names, and the probe it names (A21).** The mathematician specifies; you build it and make it typecheck. Your report is the other half of that channel, so write what the next brief will need.

**THE RATIO BAR IS LIVE AND IT IS 0.0123 SECONDS PER IN-FENCE LINE.** A green return at or above that rate is ESCALATED to a critic by row `sys-dd24-ratio-bar`, which is DD24 restored by amendment A10. The divisor is fact 7, the in-fence line count of THIS task's write scope, counted the ledger's way: non-blank lines inside ` ```agda ` fences. **A raw `.agda` probe carries no fence and counts 0**, so the bar cannot fire on a probe and it binds the moment you write a `.lagda.md` master under `src/`. Design for it rather than discovering it: the number comes from `dev/pod/table.toml` at brief build, and its measured basis is in `dev/ledger.toml [ratio]`.

## LAWS (program-generated, do not edit)

MANDATORY for kind `recon` (read-only: an audit, a design pass, a history dig. It writes a report and nothing else. The sweep C-42 demands is a recon action, so this is that law's home bundle.):

- **D-10. Price the truth of a recorded residue before pricing its proof**
  **Rule:** A residue recorded under the wall protocol names a TARGET, and a target can be false; before dispatching a discharge batch, spend the five minutes checking the target's truth at the intended generality (a Tarskian or cardinality obstruction is the usual killer), and record the corrected target beside the original.
  Full entry: dev/LESSONS.md:1375
- **C-22. A dispatched agent writes its deliverable incrementally, never at the end**
  **Rule:** When an agent's deliverable is a file, the brief must require it WRITTEN EARLY as a skeleton and filled incrementally, saving after each answer lands. An agent that researches for its whole budget and leaves the writing to the end returns nothing when the budget runs out, and its research dies with it. A partial dossier is a real deliverable; an unwritten perfect one is not.
  Full entry: dev/LESSONS.md:2297
- **P-l. A statement may be ABOUT a concrete stage without dragging that stage's PRESENTATION into its type**
  **The law.** Being about a concrete position is not what costs. Naming a transparent construction in a statement's TYPE is. If the tower's stage values are `opaque` upstream, a theorem may quantify over, hypothesize about and conclude at `Sset ω` freely, because the stage is an ATOM to the elaborator and nothing unfolds. If instead the type mentions a transparent presentation, such as `⟪ sucV (...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2357
- **D-26. A well-founded key on a tower needs generation data, or it needs syntax**
  **Rule:** When a route must well-order a cumulative tower's stage, ask first what the stage's members CARRY. A stage built as the values of finitely many total operations carries its own generation data, so a well-founded key exists with NO syntax at all: the operation index, then the arguments, ordered recursively. A stage built as a definable power carries nothing: its members are sets, not c...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:1735
- **C-42. A refutation measures the site it names, and it never measures how far that site extends**
  **Rule:** A refutation is a measurement of ONE site. It says the statement there is false. **It says nothing about how many other sites carry the same false shape.** So when a refutation lands, the next action is not the cure. **It is the sweep: search the tree for the shape, and report the COUNT before you price the cure.** A cure funded against the named site is priced against a number nobody...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:3752

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev, archive/scripts, dev/ARCHIVE.md:
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 218.591)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 203.028)
- CANDIDATE archive/dev/JOURNAL.md  (score 163.680)
- CANDIDATE dev/ARCHIVE.md  (score 142.303)
- CANDIDATE archive/dev/DD-archived.md  (score 140.452)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 57.645)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 53.054)
- CANDIDATE dev/literature/terms-2026-08.md  (score 49.180)
- CANDIDATE dev/literature/digest.md  (score 42.507)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 34.326)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
