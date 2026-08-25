# LJ-1.459: land the counting leg's implication, and state its residue as a type

## HEAD
head_slot: coder
machine: exclusive

## THE OBLIGATION

Land ONE term in `src/L/StageBound.lagda.md`:

    bounded-from-data :
        ((δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → sq δ)
      → ⟨ x ∈ˢ Lset κ ⟩

in the module that already carries `bounded-from-trunc`, and state `Residue` in
that same chapter as a type beside `SqCollect`. **The body is the identity
adapter, then `∣_∣₁`, then the chapter's own `bounded-from-trunc`.**

**READ ONE REPORT BEFORE ANYTHING ELSE.** `agents/tasks/LJ-1-456/lj-1.456-report.md`,
verdict `GO` at `:89`, committed at `55f65b4`. Its `adapter` is the identity in
four lines (`agents/tasks/LJ-1-456/Probe456.agda:55-58`). If that report does
not exist or its verdict is not `GO`, write nothing and stop.

**DO NOT LAND `bounded-from-residue` AS `[LJ-1.456]` STATES IT.** That term takes
`Residue` and never spends it: its body is `bounded-from-residue _ = ...`
(`Probe456.agda:102`). The dependence on `Residue` is real but it lives inside
`sq-data-closed`, which is a module hypothesis there. **A landed signature with
an unused parameter overstates what the term proves.** Land the implication that
has content, and state `Residue` separately as a type.

## OBLIGATION NAMES
obligations = ["src/L/StageBound.lagda.md::bounded-from-data"]

## SCOPE (write)
- src/L/StageBound.lagda.md
- dev/ledger.toml
- agents/tasks/LJ-1-459/lj-1.459-report.md
- agents/tasks/LJ-1-459/review-of-bounded-from-data.md
- agents/tasks/LJ-1-459/runs/

## PREMISES

1. `[LJ-1.456]` is GO on the chain end to end, against this chapter. Basis: agents/tasks/LJ-1-456/lj-1.456-report.md:89
2. Its `adapter` is the identity, written and typechecked. Basis: agents/tasks/LJ-1-456/Probe456.agda:55
3. Its obligation ignores its own `Residue` parameter. Basis: agents/tasks/LJ-1-456/Probe456.agda:102
4. The consumer is already landed in this chapter. Basis: src/L/StageBound.lagda.md:109
5. `SqFam` is landed beside it and is the adapter's codomain. Basis: src/L/StageBound.lagda.md:35
6. `SqCollect`, the TRUNCATED route's residue, is already stated in this chapter as a type. Basis: src/L/StageBound.lagda.md:43
7. `[LJ-1.452]` is GO on the supply half as DATA under one hypothesis. Basis: agents/tasks/LJ-1-452/lj-1.452-report.md:75
8. `[LJ-1.447]` is GO on the split that carries `Residue`. Basis: agents/tasks/LJ-1-447/lj-1.447-report.md:53
9. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
10. `make check` is the gate before any commit. Basis: AGENTS.md:75
11. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69
12. One SRC collection after LJ-1. Basis: dev/pod/direction.md:37

## WHAT IS DELIVERED ALREADY

`src/L/StageBound.lagda.md` holds `SqFam` (`:35`), `SqCollect` (`:43`),
`bounded-from-trunc` (`:109`) and `bounded-modulo-collect` (`:114`). **The
truncated route's residue is a type in the tree and the DATA route's is not.**

## WHAT IS MISSING

The DATA-side implication, and `Residue` as a type. `[LJ-2.5]` should read both
residues in one chapter.

## THE REASONING

**D-10, BEFORE ANY AGDA.** Quote `SqFam` (`src/L/StageBound.lagda.md:35-41`) and
`[LJ-1.456]`'s `adapter` domain (`Probe456.agda:56-58`). Say in one line whether
the obligation's hypothesis IS `SqFam α` after the adapter, and give the
evidence.

**THE SHAPE.** Add `bounded-from-data` inside the module that carries
`bounded-from-trunc`, so it inherits the same telescope including `levelIn` and
`cover`. State `Residue` at `[LJ-1.447]`'s delivered shape, generic. Update
`dev/ledger.toml`.

**`Residue` IS STATED AND NEVER INHABITED.** Nothing in this tree proves it and
nothing refutes it. Do not postulate it. DD9 says a new principle is stated as
a type.

**REQUIRED REPORT SECTION `## WHAT THE CHAPTER NOW OWES`.** List, as types and
at `file:line`, every hypothesis the bounded-subset conclusion still rests on
after this lands: `Residue`, `levelIn` and `cover`. **Say plainly that the
condensation pair is unpaid and that this task does not touch it.**

**THIS TASK RUNS `machine: exclusive`, AND THE REASON IS MEASURED.** Every
seconds key is guarded by `concurrency == 1` (`scripts/pod/table.py:575`), and
`[LJ-1.453]` was the first landing ever to record it. **Run ONE Agda process.**

**THE RATIO BAR IS LIVE AND THE ROW IS FIXED.** `[LJ-1.453]` measured 0.0394 on
the accept record and 0.1883 on its own three rechecks, both above 0.0123.
**Report both numbers and the record's `concurrency` in a section
`## THE RATIO`.** Do not pad.

**PROSE IS FROZEN.** Code and the comments inside it only (`AGENTS.md:69`).

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 20 in-fence lines added. BASIS:
`[LJ-1.456]`'s whole obligation is 6 lines under a stated telescope
(`Probe456.agda:101-106`) and `Residue` is one type definition. Comparables are
of SHAPE.

## W3, THE WIDEST UNMEASURED TERM

It is whether the chapter's own telescope admits the term without a new module.

    inside : SqFam α → ⟨ x ∈ˢ Lset κ ⟩
    inside f = bounded-from-trunc ... ∣ f ∣₁

**Write it FIRST inside the existing module, with `bounded-from-data` and
`Residue` omitted, and typecheck the chapter.** `[LJ-1.456]` rebuilt the
telescope in a probe; a chapter must not. If the term needs a new module
application, that is the finding and the report names it.

ESTIMATE for W3: three lines and under 20 seconds on top of the chapter.

Report the median wall time and peak RSS over three forced rechecks, and run
`make check` before and after.

## WHAT GO AND NO-GO EACH EARN

**A GO PUTS BOTH ROUTES' RESIDUES IN ONE CHAPTER**, which is what `[LJ-2.5]`
must rule on.

**A NO-GO SAYS THE CHAPTER'S TELESCOPE WILL NOT CARRY IT**, which would mean
`[LJ-1.456]`'s probe telescope is not the chapter's.

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
  seconds_per_line_max = 0.0123

[[branch]]
# THE DELTA KEY IS DELIBERATELY ABSENT. MEASURED 2026-08-21 on LJ-1.453: its
# closing record carried obligations_delta 0 because the obligation landed on
# the previous attempt, so a ratio row keyed on -1 missed and the close fell
# through to sys-obligations-satisfied. Replayed without the key, this row
# matches AND wins, because AD8 puts a task row ahead of a system row.
id = "ratio-bar"
priority = 11
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 0
  heap_wall = false
  seconds_per_line_min = 0.0123

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-459/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-459-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-459/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["src/L/StageBound.lagda.md"]
  changed_files_none = ["agents/tasks/LJ-1-459/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-459/review-of-*.md"]

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
