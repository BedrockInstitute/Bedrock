# LJ-1.503: which omega gate wins, settled at the one site that consumes it

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-503/Probe503.agda`:

    envSetK-at-KValue-gate : (envSetK, rebuilt with ⟨ ω ∈ gam ⟩ in place of
                             ⟨ ω ∈ sucV gam ⟩)

**and thereby say which of the two gates the chapter actually needs.** Land
nothing in `src/`.

**`[LJ-1.499]` IS GO AND IT NAMES THIS AS THE ONE OPEN STEP AT THIS FRAME**
(`agents/tasks/LJ-1-499/lj-1.499-report.md:283-287`):

> **The ω hypothesis is the one open step at this frame.** `KValue` has none,
> `[LJ-1.491]` added `⟨ ω ∈ gam ⟩`, and `SupplyEnv` wants `⟨ ω ∈ sucV gam ⟩`.
> One of these must win before a `TFacts` value is built.

**THE CENSUS IS SMALL AND I HAVE RUN IT.** In `src/L/Coding/EnvSupply.lagda.md`
the gate is the module hypothesis at `:111` and it has **exactly one consumer**,
`envSetNumeral∈` applied inside `envSetK` at `:146`. Everything else the chapter
does with the gate passes it straight through. **So one site decides the
question.** The `ω∈γ` occurrences in `src/L/SquareLawClosed.lagda.md:120-158` are
a DIFFERENT hypothesis in a different chapter and must not be counted here.

**WHY `⟨ ω ∈ gam ⟩` IS THE ONE TO TRY.** `[LJ-1.491]` is GO and built exactly
that at `KValue`, with zero landed consumers losing an instance
(`agents/tasks/LJ-1-491/lj-1.491-report.md:200`). It is STRONGER than the
`sucV` gate, so it implies it; the cost of the stronger gate is that it excludes
`gam = ω`. **If the chapter runs on it, `KValue`'s own gate drives `SupplyEnv`
and nothing needs restating.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-503/Probe503.agda::envSetK-at-KValue-gate"]

## SCOPE (write)
- agents/tasks/LJ-1-503/Probe503.agda
- agents/tasks/LJ-1-503/lj-1.503-report.md
- agents/tasks/LJ-1-503/review-of-envSetK-at-KValue-gate.md
- agents/tasks/LJ-1-503/runs/

## PREMISES

1. `[LJ-1.499]` is GO and names the ω hypothesis as the one open step. Basis: agents/tasks/LJ-1-499/lj-1.499-report.md:283
2. The gate is a module hypothesis of `SupplyEnv`. Basis: src/L/Coding/EnvSupply.lagda.md:111
3. Its one consumer in that chapter is `envSetNumeral∈`, inside `envSetK`. Basis: src/L/Coding/EnvSupply.lagda.md:146
4. `envSetNumeral∈` is imported from `L.Coding.Key`. Basis: src/L/Coding/EnvSupply.lagda.md:69
5. `[LJ-1.491]` is GO on `⟨ ω ∈ gam ⟩` at `KValue`, with no landed consumer losing an instance. Basis: agents/tasks/LJ-1-491/lj-1.491-report.md:200
6. `KValue` is the module that binds `gam`. Basis: src/L/Condensation.lagda.md:7380
7. `SupplyEnv.envK-gen` is the real supplier of the nine env fields. Basis: src/L/Coding/EnvSupply.lagda.md:277
8. `[LJ-1.499]` built the five `envK-*` fields from it at `TFacts`'s frame. Basis: agents/tasks/LJ-1-499/lj-1.499-report.md:20
9. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
10. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
11. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THIRTY NINE OF FIFTY NINE `TFacts` FIELDS ARE NOW ACCOUNTED**: twenty six from
`[LJ-1.495]`, four from `[LJ-1.501]`, and nine from `[LJ-1.499]`, which found
that `src/L/Coding/EnvSupply.lagda.md:293-411` already holds the whole `envK-*`
and `envInK-*` families and that they reach `TFacts`'s frame with one `refl`
each. **The gate is what stands between those and a `TFacts` value.**

## WHAT IS MISSING

One substitution, and the answer it gives.

## THE REASONING

**D-10, BEFORE ANY AGDA.** Open `L.Coding.Key` and read `envSetNumeral∈`'s
signature. **Say at `file:line` what gate it asks for.** If it asks for neither
candidate but for something weaker, **say so and build at THAT gate instead**:
the weakest sufficient hypothesis is the right answer and the brief's chosen
candidate is not binding on you.

**REBUILD, DO NOT PATCH.** Rebuild the `SupplyEnv` telescope down to `envSetK`
with the gate replaced, and typecheck `envSetK` alone. Do not import a probe and
do not edit `src/`.

**DO NOT WEAKEN `envSetK`'s CONCLUSION TO MAKE THE GATE FIT.** If the stronger
gate does not drive it, the finding is that `SupplyEnv`'s own gate wins, and
that is a clean answer worth as much as the other one.

**DO NOT BUILD A `TFacts` VALUE, AND DO NOT REBUILD THE NINE ENV FIELDS.**
`[LJ-1.499]` delivered those and its report forbids asking for them again.

**REQUIRED REPORT SECTION `## WHICH GATE WINS`.** Name the gate
`envSetNumeral∈` asks for at `file:line`, say whether `⟨ ω ∈ gam ⟩` drives it,
and state in one sentence which of the three candidates a `TFacts` value should
carry. **Do not change anything in `src/` to suit the answer.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 120 lines in the probe, of which the obligation is
about 30, the rest being the rebuilt telescope. BASIS: `[LJ-1.499]` rebuilt this
chapter's frame in a comparable file. Comparables are of SHAPE and nothing may be
funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the implication between the two gates, because everything turns on it and
`[LJ-1.491]` asserted it without building it.

    gam-to-sucV : ⟨ ω ∈ gam ⟩ → ⟨ ω ∈ sucV gam ⟩

**Write it FIRST, with the obligation omitted, and typecheck it ALONE.**
`[LJ-1.491]`'s report says `ω ∈ gam` implies the `sucV` gate by the first
disjunct of `∈sucV`, but says it in prose. **If the implication does not
typecheck, the two gates are not comparable and the whole question changes
shape**, and the task stops there having found something better than it was sent
for.

ESTIMATE for W3: about 8 lines and under 20 seconds. **Do not fund it against
`[LJ-1.491]`'s 2.40 s**: that built a record telescope and this is one
disjunction.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO SETTLES THE LAST OPEN STEP BETWEEN THIRTY NINE FIELDS AND A `TFacts`
VALUE**, and it settles it in favour of the gate `[LJ-1.491]` already built, so
nothing needs restating.

**A NO-GO SAYS `SupplyEnv`'s OWN GATE WINS**, which tells the mathematician that
`KValue` must carry `⟨ ω ∈ sucV gam ⟩` and not the stronger form, and that
`gam = ω` stays legal. Either answer closes the question.

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
id = "accept-failed"
priority = 14
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 1
  changed_files_none = ["agents/tasks/LJ-1-503/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-503/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-503/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-503/Probe503.agda"]
  changed_files_none = ["agents/tasks/LJ-1-503/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-503/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 176.608)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 161.315)
- CANDIDATE archive/dev/JOURNAL.md  (score 157.634)
- CANDIDATE archive/dev/DD-archived.md  (score 131.281)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 128.337)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 55.891)
- CANDIDATE dev/literature/devlin-II5.md  (score 47.787)
- CANDIDATE dev/literature/digest.md  (score 40.124)
- CANDIDATE dev/literature/terms-2026-08.md  (score 38.793)
- CANDIDATE dev/literature/geology.md  (score 29.052)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
