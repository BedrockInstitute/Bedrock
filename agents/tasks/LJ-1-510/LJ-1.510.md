# LJ-1.510: the three consK fields, the only ones with no supplier anywhere

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-510/Probe510.agda`:

    consK-exist-at-frame : (TFacts's consK-exist, at KValue's frame)

**or refute it and name the hypothesis it needs.** Land nothing in `src/`.

**THESE THREE ARE THE ONLY FIELDS OF THIS RECORD WITH NO CANDIDATE SUPPLIER.**
I ran the sweep: `consK` occurs **six times in `src/`, all of them inside
`src/L/Condensation/TwelveAgree.lagda.md`** (the three declarations at `:317`,
`:322`, `:332` and their fills). **Nothing outside that file names a `consK` of
any shape.** Every other family of this record had a supplier waiting:
`[LJ-1.499]` found the nine env fields in `src/L/Coding/EnvSupply.lagda.md`,
and `[LJ-1.509]` found `subK-gen` there too (`:481-487`), already instantiated
at five of the six `subK` prefixes (`:506`, `:517`, `:528`, `:539`, `:550`).
**This family has nothing.**

**THE SHAPE IS DIFFERENT AND THAT IS WHY IT IS LAST.** `consK-exist`
(`src/L/Condensation/TwelveAgree.lagda.md:317-321`) takes a `consAtL`
satisfaction conjoined with a membership atom, over an EIGHT cell prefix, and
concludes at `lookup (suc¹⁴ K)` of that extended environment. `consAtL` itself is
delivered and widely used (`src/L/Condensation.lagda.md:31`, with instances at
`:172`, `:1060`, `:1193`). **The formula is not the problem. The closure is.**

**`[LJ-1.495]` IS THE METHOD AND ITS REACH IS THIS TASK'S W3.** It is GO and
delivers `KFacts` at `suc⁶` by six `KFactsCons` steps. These fields need
`suc¹⁴` over an eight cell prefix, which is the SAME shift eight steps further.
**Nobody has iterated it past six.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-510/Probe510.agda::consK-exist-at-frame"]

## SCOPE (write)
- agents/tasks/LJ-1-510/Probe510.agda
- agents/tasks/LJ-1-510/lj-1.510-report.md
- agents/tasks/LJ-1-510/review-of-consK-exist-at-frame.md
- agents/tasks/LJ-1-510/runs/

## PREMISES

1. `consK-exist` concludes at a fourteen deep `K` index. Basis: src/L/Condensation/TwelveAgree.lagda.md:317
2. `consK-forall` is its sibling. Basis: src/L/Condensation/TwelveAgree.lagda.md:322
3. `consK-allin` is the third. Basis: src/L/Condensation/TwelveAgree.lagda.md:326
4. `consAtL` is delivered and imported by the consumer chapter. Basis: src/L/Condensation.lagda.md:31
5. It is used at a comparable prefix elsewhere. Basis: src/L/Condensation.lagda.md:1060
6. `[LJ-1.495]` is GO and delivers `KFacts` six steps deep. Basis: agents/tasks/LJ-1-495/lj-1.495-report.md:71
7. `KFactsCons` is the one step shift. Basis: src/L/Condensation.lagda.md:6122
8. `[LJ-1.509]` is GO and found `subK-gen` already delivered. Basis: agents/tasks/LJ-1-509/lj-1.509-report.md:56
9. `subK-gen` is generic in the environment length and all four indices. Basis: src/L/Coding/EnvSupply.lagda.md:481
10. `[LJ-1.499]` found the env family delivered in the same chapter. Basis: agents/tasks/LJ-1-499/lj-1.499-report.md:20
11. `KValue` binds the carrier and the stage. Basis: src/L/Condensation.lagda.md:7380
12. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
13. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
14. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**FORTY EIGHT OF FIFTY NINE POSITIONS ARE ACCOUNTED OR IN FLIGHT.** Twenty six
from `[LJ-1.495]`, four from `[LJ-1.501]`, nine from `[LJ-1.499]`, two from
`[LJ-1.500]`, seven from `[LJ-1.509]`, and `someEnv` with `valK` in flight.
**These three are the last corner nobody has opened.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE REACH OF THE SHIFT.** Say at `file:line`
how deep `[LJ-1.495]`'s construction goes and whether `KFactsCons` composes
eight more times over the eight cell prefix these fields use. **If the shift
stops short, name the step at which it stops and STOP.** That would say the
record states fields its own frame cannot reach, which is a design finding about
the last corner and it is worth the dispatch on its own.

**LOOK FOR A SUPPLIER BEFORE YOU BUILD ONE.** `[LJ-1.499]` and `[LJ-1.509]` both
found the tree had already written what a brief asked them to build. **Sweep
`src/L/Coding/` for a closure over `consAtL` and report the COUNT before you
write a term.** If one exists, use it and say so.

**IF THE BARE FORM IS FALSE, REFUTE IT.** `[LJ-1.506]` showed how at this record.
A machine-checked counterexample with the weakest repairing hypothesis named is a
full deliverable.

**TAKE THE WEAKEST HYPOTHESIS AND DO NOT PIN A SLOT.** The mathematician has
ruled that way three times. A hypothesis fixing what occupies a slot would
pre-empt `[LJ-1.505]` and will be refused.

**DO NOT USE A `TFacts` FIELD TO PROVE A `TFacts` FIELD**, and do not postulate.

**DO NOT BUILD `consK-forall` OR `consK-allin`.** AD12 gives this brief one
obligation. Census them; do not build them.

**REQUIRED REPORT SECTION `## THE THREE consK FIELDS`.** One row each (`:317`,
`:322`, `:326`) saying whether this argument serves it unchanged, after a prefix
change, or not at all.

**REQUIRED REPORT SECTION `## HOW DEEP THE SHIFT GOES`.** State the maximum
depth `KFactsCons` reaches at this frame, measured and not estimated.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 180 lines in the probe, of which the obligation is
about 45. BASIS: `[LJ-1.509]` rebuilt this frame and a generic closure in a
comparable file. Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the depth, because every accounted field of this record sits at six and
these sit at fourteen.

    deep-shift : KFacts at suc¹⁴, over the eight cell prefix

**Write it FIRST, with the obligation omitted, and typecheck it ALONE.** If the
shift composes to fourteen, the rest is the closure argument. If it does not, the
task stops at its cheapest point and the finding is about the record's frame
rather than about one field.

ESTIMATE for W3: about 25 lines and under 40 seconds. **Do not fund it against
`[LJ-1.495]`'s 2.44 s**: that measured two steps and this measures fourteen.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO OPENS THE LAST CORNER OF THIS RECORD** and would leave every family of
`TFacts` either paid, in flight, or named.

**A NO-GO AT THE DEPTH SAYS THE FRAME CANNOT REACH ITS OWN DEEPEST FIELDS**,
which is the sharpest possible statement about the record's design and would
decide whether a `TFacts` value is reachable at all.

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
  changed_files_none = ["agents/tasks/LJ-1-510/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-510/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-510/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-510/Probe510.agda"]
  changed_files_none = ["agents/tasks/LJ-1-510/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-510/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 205.631)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 179.235)
- CANDIDATE dev/ARCHIVE.md  (score 164.848)
- CANDIDATE archive/dev/JOURNAL.md  (score 158.818)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 143.192)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 56.231)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 55.185)
- CANDIDATE dev/literature/digest.md  (score 48.605)
- CANDIDATE dev/literature/terms-2026-08.md  (score 41.410)
- CANDIDATE dev/literature/geology.md  (score 34.935)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
