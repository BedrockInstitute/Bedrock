# LJ-1.512: TFacts declares fields the tree proves in a stronger form elsewhere

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-512/Probe512.agda`:

    honest-covers-record :
        (EnvSupply's consK-exist, at KValue's frame)
      → (TFacts's consK-exist at that frame, given the hypothesis the honest
         form takes)

**a correspondence showing the delivered honest form IS the record's field plus
its missing hypothesis.** Land nothing in `src/`.

**THREE FIELDS OF THIS RECORD ARE NOW MEASURED FALSE AS WRITTEN, AND EACH TIME
THE TREE ALREADY HELD A HONEST FORM.**

| field | who refuted it | the honest form |
|---|---|---|
| `someEnvDef` | `[LJ-1.507]`, empty antecedent, `--safe` | needed the truncation in its own type; `[LJ-1.511]` is GO at the corrected type |
| `valK` | `[LJ-1.508]`, false with the FULL `KFacts` supplied (`Probe508.agda:324-329`) | needs `valSub`, every member of slot one is in `K` |
| `consK-exist` | `[LJ-1.510]`, machine-checked (`Probe510.agda:395-405`) | `src/L/Coding/EnvSupply.lagda.md:661-668`, which takes `⟨ fst ya ∈ fst K ⟩` and proves it in two lines |

**THE QUESTION THIS TASK ANSWERS IS WHETHER THAT IS A PATTERN OR THREE
ACCIDENTS.** `[LJ-1.499]` found the nine env fields delivered in that chapter.
`[LJ-1.509]` found `subK-gen` delivered and instantiated there. `[LJ-1.510]`
found `consK-exist` there. **Four dispatches, one chapter, every time.**

**A CORRECTION YOU SHOULD KNOW ABOUT, BECAUSE IT IS WHY THIS BRIEF EXISTS.**
`[LJ-1.510]`'s brief told you `consK` occurs six times in `src/`, all in one
file. **That was false**: it is 44 occurrences in four files, and 14 of them are
in `src/L/Coding/EnvSupply.lagda.md`. The mathematician read a truncated command
output as a complete count. **Do not trust a count in a brief. Re-run it.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-512/Probe512.agda::honest-covers-record"]

## SCOPE (write)
- agents/tasks/LJ-1-512/Probe512.agda
- agents/tasks/LJ-1-512/lj-1.512-report.md
- agents/tasks/LJ-1-512/review-of-honest-covers-record.md
- agents/tasks/LJ-1-512/runs/

## PREMISES

1. `[LJ-1.510]` is GO and refuted the record's field as written. Basis: agents/tasks/LJ-1-510/lj-1.510-report.md:15
2. Its counterexample is machine checked. Basis: agents/tasks/LJ-1-510/Probe510.agda:395
3. The honest form is delivered and takes the missing hypothesis. Basis: src/L/Coding/EnvSupply.lagda.md:661
4. `[LJ-1.508]` is GO and refuted `valK` with the full `KFacts` supplied. Basis: agents/tasks/LJ-1-508/Probe508.agda:324
5. Its measured hypothesis is about slot one and pins nothing. Basis: agents/tasks/LJ-1-508/Probe508.agda:201
6. `[LJ-1.507]` refuted `someEnvDef-gap` as empty. Basis: agents/tasks/LJ-1-507/Probe507.agda:257
7. `[LJ-1.511]` is GO at the corrected definition. Basis: agents/tasks/LJ-1-511/Probe511.agda:195
8. `[LJ-1.509]` found `subK-gen` delivered in the same chapter. Basis: src/L/Coding/EnvSupply.lagda.md:481
9. `[LJ-1.499]` found the env family delivered there. Basis: agents/tasks/LJ-1-499/lj-1.499-report.md:20
10. `[LJ-1.510]` measured the shift to be unbounded in depth. Basis: agents/tasks/LJ-1-510/Probe510.agda:85
11. `TFacts` is the record under question. Basis: src/L/Condensation/TwelveAgree.lagda.md:129
12. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
13. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
14. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**FIFTY OF FIFTY NINE POSITIONS ARE ACCOUNTED**, and three of the fields
counted among them are now known to be FALSE as the record declares them. **The
count is not the problem. The record's types are.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** Open `src/L/Coding/EnvSupply.lagda.md` and **census
it against `TFacts` by NAME**. For each of the 59 fields say: an honest form
exists there, an honest form exists elsewhere, or none is delivered. **Re-run
every count yourself and print the command.** The mathematician's counts have
been wrong twice.

**THEN BUILD THE ONE CORRESPONDENCE.** Take the honest `consK-exist`
(`src/L/Coding/EnvSupply.lagda.md:661-668`), instantiate it at `KValue`'s frame,
and derive the record's field from it under the honest form's own hypothesis.
**If they do not correspond, say where they diverge**: that would mean the two
are different statements and not one statement at two strengths.

**DO NOT BUILD THE OTHER FIFTY EIGHT CORRESPONDENCES.** AD12 gives this brief
one obligation. The census is a report section, not a proof obligation.

**DO NOT EDIT `src/` AND DO NOT PROPOSE A REDESIGN.** Whether `TFacts` should be
replaced by the honest forms is a record redesign and it is the mathematician's.
Your census is the evidence for that decision.

**DO NOT POSTULATE, AND DO NOT USE A `TFacts` FIELD TO PROVE A `TFacts` FIELD.**

**REQUIRED REPORT SECTION `## THE HONEST FORM CENSUS`.** A table over all 59
fields with the three verdicts above and a `file:line` for every honest form you
find. **This section is the deliverable even if the obligation is not built.**

**REQUIRED REPORT SECTION `## HOW MANY DIFFER`.** Of the honest forms found, how
many take a hypothesis the record's field does not. **That number is what the
mathematician needs.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 150 lines in the probe, of which the obligation is
about 35, the rest being the frame. BASIS: `[LJ-1.510]` rebuilt this frame to
depth fourteen in a comparable file. Comparables are of SHAPE and nothing may be
funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the census, because the obligation is one instance of a pattern and the
pattern's size is what decides the next ruling.

    -- the 59 rows, by name, against src/L/Coding/EnvSupply.lagda.md

**Do this FIRST, before any term, and write it into the report as you go (C-22).**
If the honest forms cover most of the record, the mathematician has a redesign to
rule on. If they cover three, these are three accidents and the record stands.

ESTIMATE for W3: mostly reading, under 20 seconds of Agda. **Do not fund it
against any predecessor**: no dispatch has censused this chapter by name.

Report the median wall time and peak RSS over three forced rechecks, for the
full file.

## WHAT GO AND NO-GO EACH EARN

**A GO WITH A LARGE CENSUS SAYS THE RECORD SHOULD BE REPLACED BY THE FORMS THE
TREE ALREADY PROVES**, which would be the largest single simplification this
campaign could make.

**A GO WITH A SMALL CENSUS SAYS THE THREE REFUTATIONS ARE LOCAL**, and the
remaining fields can be paid one at a time as they have been.

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
  obligations_delta_max = -1
  changed_files_none = ["agents/tasks/LJ-1-512/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-512/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-512/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-512/Probe512.agda"]
  changed_files_none = ["agents/tasks/LJ-1-512/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-512/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 235.365)
- CANDIDATE archive/dev/JOURNAL.md  (score 227.480)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 208.525)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 172.691)
- CANDIDATE archive/dev/DD-archived.md  (score 172.110)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 62.884)
- CANDIDATE dev/literature/devlin-II5.md  (score 52.415)
- CANDIDATE dev/literature/terms-2026-08.md  (score 46.817)
- CANDIDATE dev/literature/digest.md  (score 45.176)
- CANDIDATE dev/literature/geology.md  (score 41.309)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
