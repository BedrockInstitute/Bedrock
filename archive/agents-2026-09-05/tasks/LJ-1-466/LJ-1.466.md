# LJ-1.466: the constants the hull cannot yet name

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-466/Probe466.agda`:

    lset-codes : Vec Code (countFo LsetGraph)

the hull codes for the constants of the level formula, so that `wit` can be
applied. Land nothing in `src/`.

**`[LJ-1.462]` GOT EVERYTHING ELSE AND STOPPED AT EXACTLY THIS.** Its report is a
critic-upheld NO-GO (`:75`, committed `041135c`) and it says: the formula IS
delivered, the packaging is `absFo` and not a `subst`, `feed` applies `wit` to
`absFo LsetGraph` and typechecks, **and it needs a further
`Vec Code (countFo LsetGraph)` that is not delivered**, because
`constantsFo LsetGraph` is `Vec CS.S` and not `Vec Code`.

**READ THAT REPORT FIRST AND QUOTE THE `feed` LINE.** If its verdict is not a
stated NO-GO, or the packaging it names is absent, write nothing and stop.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-466/Probe466.agda::lset-codes"]

## SCOPE (write)
- agents/tasks/LJ-1-466/Probe466.agda
- agents/tasks/LJ-1-466/lj-1.466-report.md
- agents/tasks/LJ-1-466/review-of-lset-codes.md
- agents/tasks/LJ-1-466/runs/

## PREMISES

1. `[LJ-1.462]` is a critic-upheld NO-GO whose obstruction is this vector. Basis: agents/tasks/LJ-1-462/lj-1.462-report.md:75
2. It built `feed`, `wit` applied to the packaged formula, and it typechecks. Basis: agents/tasks/LJ-1-462/Probe462.agda:101
3. The packaging is `absFo`, and the hull itself uses it. Basis: src/L/Hull.lagda.md:126
4. `absFo`'s type is delivered. Basis: src/FOL/Manipulation/Parameters.lagda.md:260
5. `constantsFo` returns a `Vec K` at the formula's own parameter type. Basis: src/FOL/Manipulation/Parameters.lagda.md:105
6. The hull's `base` turns a carrier element into a code. Basis: src/L/Hull.lagda.md:73
7. The level formula is delivered. Basis: src/L/Coding/Sequence.lagda.md:349
8. `[LJ-1.458]` is GO on finding it and its adequacy. Basis: agents/tasks/LJ-1-458/lj-1.458-report.md:71
9. `levelIn` is one of the two unpaid condensation hypotheses. Basis: src/L/BoundedSubset.lagda.md:917
10. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
11. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**`[LJ-1.462]` LEFT ONE STEP AND NAMED IT.** It inhabited step 1
(`Probe462.agda:133-134`), stated steps 2 and 3 as types, packaged the formula,
and got `wit` to accept it. The only thing missing is the vector of codes for
the formula's constants.

## WHAT IS MISSING

A code for each constant. `base` makes a code from a CARRIER element, and the
constants are L-sets. **The question is whether each constant lies in the hull's
carrier.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE WHOLE QUESTION.** Write down
`constantsFo LsetGraph` and say, for each entry, whether it lies in the hull's
carrier `⟪ X ⟫`. **The hull is built over a chosen `X`
(`src/L/Hull.lagda.md:313`), so this is a question about `X` and not about the
formula.** If the constants are not in `X` for a general `X`, say what `X` must
contain and STOP: that condition is the finding, and it would tell the
condensation front what its hull must be built over.

**THE SHAPE.** Rebuild `[LJ-1.462]`'s telescope down to the hull, copying
`src/L/BoundedSubset.lagda.md:903-914` as that probe did. Take the packaged
formula at `[LJ-1.462]`'s delivered shape. Map `base` over the constants once
each constant is placed in the carrier. Do not import a probe.

**DO NOT BUILD `levelIn` AND DO NOT BUILD `lset-code`.** One obligation: the
vector. `[LJ-1.462]` states the rest as types and a later brief joins them.

**DO NOT POSTULATE AND DO NOT ADD A HYPOTHESIS PLACING A CONSTANT IN `X` BY
FIAT.** If a constant needs to be in `X`, that is a CONDITION ON THE HULL and it
belongs in the report, not in the telescope.

**REQUIRED REPORT SECTION `## WHAT THE HULL MUST CONTAIN`.** List every constant
of `LsetGraph` and, for each, the condition on `X` that puts it in the carrier.
**That list is worth more than the obligation if the obligation does not close.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 120 lines in the probe, of which the obligation is
about 20. BASIS: `[LJ-1.462]`'s own probe measured 63 non-blank non-comment
lines over 149 total, and this file rebuilds its telescope and adds one vector.
Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is `countFo LsetGraph`, because the vector's LENGTH decides whether this is
one code or many.

    how-many : ℕ
    how-many = countFo LsetGraph

**Evaluate it FIRST, with the obligation omitted, and report the number.** If it
is zero the vector is `[]` and the obligation is immediate; if it is large the
task is a census of constants and the report must say so before building
anything.

ESTIMATE for W3: two lines and under 10 seconds. **The number itself is the
measurement and this brief does not guess it.**

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO CLOSES THE LAST NAMED STEP OF `levelIn`'s HULL ROUTE**, and a later brief
joins `[LJ-1.462]`'s stated types into the obligation.

**A NO-GO NAMES THE CONDITION ON THE HULL**, which is the first statement in this
campaign about what the condensation hull must be built over.

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
  changed_files_any = ["agents/tasks/LJ-1-466/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-466-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-466/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-466/Probe466.agda"]
  changed_files_none = ["agents/tasks/LJ-1-466/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-466/review-of-*.md"]

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
