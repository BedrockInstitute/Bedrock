# LJ-1.702: free LJ-1.643's delivered work from its park

## HEAD
head_slot: coder
machine: shared
agda_tier: wide

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-702/Probe702.agda`:

    truncated-producer : <LJ-1.643's `Row3`: `NoInjOrd → (a : S) → IsOrd a → ∥ Σ[ θ ] (IsOrd θ × IsCardinal θ × ⟨ a ∈ˢ θ ⟩) ∥₁`>

Then do the two file repairs in SCOPE below. Land nothing in `src/`.

**NAME ANY FILE THAT CANNOT TYPECHECK `.agda.txt`, NEVER `.agda`.** Conjunct 1
runs EVERY `.agda` under this task home. That rule is half the subject of this task.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-702/Probe702.agda::truncated-producer"]

## SCOPE (write)
- agents/tasks/LJ-1-702/Probe702.agda
- agents/tasks/LJ-1-702/lj-1.702-report.md
- agents/tasks/LJ-1-702/review-of-truncated-producer.md
- agents/tasks/LJ-1-702/runs/
- agents/tasks/LJ-1-643/runs/
- agents/tasks/LJ-1-643/lj-1.643-report.md
- Never `agents/tasks/LJ-1-643/Probe643.agda`, never any `.out` file, never any `review-of-LJ-1-643-*.md`.

## PREMISES

1. **LJ-1.643 IS PARKED AND ITS WORK IS NOT IN GIT.** `git ls-files agents/tasks/LJ-1-643` returns nothing. The program commits only at a `done` close. Basis: scripts/pod/pod.py:3644
2. **ITS DELIVERABLE IS GREEN.** The acceptance record ran the probe at rc 0 in the same arm that failed. The run file is `agents/tasks/LJ-1-643/runs/accept-1.out`, arm accept-1. Basis: dev/pod/replay-corpus.jsonl:883
3. **CONJUNCT 1 IS RED BECAUSE OF A FLOOR FILE.** `runs/Floor.agda` exited 42. A floor file carries holes by construction; that is what makes it a floor. The report itself calls that file the floor, measured with a hole before the bodies landed. Basis: agents/tasks/LJ-1-643/lj-1.643-report.md:20
4. **CONJUNCT 6 IS RED FOR A SECOND, SEPARATE REASON.** Seven of the ten paths its brief injected are never named in its return. Basis: dev/pod/replay-corpus.jsonl:883
5. **THE TERM TO RE-DERIVE IS ONE ROW OF THE CENSUS.** `Row3` is the truncated producer, and `ambientCardAbove` inhabits it. Basis: agents/tasks/LJ-1-643/Probe643.agda:119
6. **THE PRODUCER IT USES IS IN THE TREE.** `NoInjOrd` is supplied by `noInjOrd`. Basis: src/L/CardinalAbove.lagda.md:575

## WHAT IS DELIVERED ALREADY

`Row3` and its inhabitant are green in LJ-1.643's own probe. Re-derive them here
by the same route. This obligation has supply 1, readable at premise 5's basis.

## THE FILE REPAIR, WHICH IS THE POINT OF THIS TASK

**FIRST, THE RENAME.** Rename EVERY `.agda` file under
`agents/tasks/LJ-1-643/runs/` to the same name with `.agda.txt`. There are
thirteen: `Floor`, and `T1` to `T12`. The content does not change and no `.out`
file changes. `agents/tasks/LJ-1-643/Probe643.agda` is the deliverable and MUST
NOT be renamed.

**SECOND, THE SURVEY DUTY.** LJ-1.643's brief injected ten candidate paths and
its return answers three. Add the seven it never names. Two belong under
`## ARCHIVE USED`: `archive/dev/JOURNAL.md` and `archive/dev/DD-archived.md`.
Five belong under `## LITERATURE USED`:
`dev/literature/truncation-and-selection.md`, `dev/literature/devlin-II5.md`,
`dev/literature/digest.md`, `dev/literature/terms-2026-08.md` and
`dev/literature/geology.md`. The existing LITERATURE paragraph already declines
those five in substance, by citation key rather than by path; the gate reads
paths. A written decline is compliance and no reading is required.

**YOU MUST NOT INVENT A FINDING, AND YOU MUST SAY WHO WROTE THE LINES.** Put the
added text under a clearly labelled sub-heading that names LJ-1.702 as its author
and the date. LJ-1.643's own agent did not write it, and a report that hides that
is a forged return. Change no other sentence of that report.

Then paste into your report the output of:

    .venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-643

and the output of `ls agents/tasks/LJ-1-643/runs/*.agda`, which must find nothing.

## THE REASONING

A park leaves its work untracked forever. LJ-1.643 delivered a green census, and
three adversarial critics overturned and twice upheld the overturn of its implied
NO-GO. It parked on a floor file and on seven unnamed survey paths, neither of
which is about the mathematics. Both repairs are additive and neither changes a
finding.

## W3, THE WIDEST UNMEASURED TERM

Whether `Row3` re-derives without the module-parameter projection LJ-1.643 needed.
Estimate 20 to 60 lines, basis: agents/tasks/LJ-1-643/Probe643.agda:126

## WHAT GO AND NO-GO EACH EARN

**GO** puts the truncated producer in a home that can close, and clears both of
LJ-1.643's red conjuncts. **NO-GO** earns the reason `Row3` does not re-derive
outside its own probe, which is a fact about imports and not about the census.

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
  changed_files_any = ["agents/tasks/LJ-1-702/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-702/review-of-LJ-*-*.md"]

[[branch]]
id = "lint-back-to-author"
priority = 13
action = "escalate"
head_slot = "coder"

  [branch.when]
  exit_code = 1
  error_class_in = ["lint"]

[[branch]]
id = "accept-failed"
priority = 14
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 1
  obligations_delta_max = -1
  changed_files_none = ["agents/tasks/LJ-1-702/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-702/Probe702.agda"]
  changed_files_none = ["agents/tasks/LJ-1-702/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-702/review-of-*.md"]

[[branch]]
# PARK, NOT ESCALATE. A heap wall is a resource fact and no critic can
# adjudicate it (MEASURED on LJ-1.534).
id = "heap-wall-park"
priority = 30
action = "park_and_split"

  [branch.when]
  heap_wall = true

[[branch]]
# Closes maintainer-backlog item 30, MEASURED on LJ-1.630. A real failed landing
# carries a named Agda error and NEITHER companion file, so both rows above miss
# it. This is the catch-all and it sits BELOW heap-wall-park.
id = "no-go-bare"
priority = 40
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
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
  Full entry: dev/LESSONS.md:2307
- **P-l. A statement may be ABOUT a concrete stage without dragging that stage's PRESENTATION into its type**
  **The law.** Being about a concrete position is not what costs. Naming a transparent construction in a statement's TYPE is. If the tower's stage values are `opaque` upstream, a theorem may quantify over, hypothesize about and conclude at `Sset ω` freely, because the stage is an ATOM to the elaborator and nothing unfolds. If instead the type mentions a transparent presentation, such as `⟪ sucV (...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2367
- **D-26. A well-founded key on a tower needs generation data, or it needs syntax**
  **Rule:** When a route must well-order a cumulative tower's stage, ask first what the stage's members CARRY. A stage built as the values of finitely many total operations carries its own generation data, so a well-founded key exists with NO syntax at all: the operation index, then the arguments, ordered recursively. A stage built as a definable power carries nothing: its members are sets, not c...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:1735
- **C-42. A refutation measures the site it names, and it never measures how far that site extends**
  **Rule:** A refutation is a measurement of ONE site. It says the statement there is false. **It says nothing about how many other sites carry the same false shape.** So when a refutation lands, the next action is not the cure. **It is the sweep: search the tree for the shape, and report the COUNT before you price the cure.** A cure funded against the named site is priced against a number nobody...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:3762

## STANDING (program-generated, do not edit)

The records every dispatch may need. They are NOT candidates, they are not the answer to any search, and no return has to account for them. The search below spends its whole budget on what is not here.

- STANDING archive/dev/JOURNAL-archived.md
- STANDING dev/literature/truncation-and-selection.md
- STANDING dev/literature/devlin-II5.md
- STANDING dev/literature/digest.md
- STANDING archive/dev/LJ-dispatch-index.md
- STANDING archive/dev/JOURNAL.md
- STANDING dev/literature/terms-2026-08.md
- STANDING dev/ARCHIVE.md
- STANDING dev/literature/geology.md
- STANDING archive/dev/DECISIONS-archived.md

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev, archive/scripts, dev/ARCHIVE.md:
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 243.240)
- CANDIDATE archive/dev/PLAN-archived.md  (score 239.200)
- CANDIDATE archive/dev/DD-archived.md  (score 233.167)
- CANDIDATE archive/dev/TASKS-archived.md  (score 172.899)
- CANDIDATE archive/dev/STATUS-archived.md  (score 168.729)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 40.420)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 36.661)
- CANDIDATE dev/literature/primary-sources.md  (score 36.284)
- CANDIDATE dev/literature/fine-structure.md  (score 32.363)
- CANDIDATE dev/literature/formalizations-landscape.md  (score 30.604)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
