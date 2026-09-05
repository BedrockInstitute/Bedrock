# LJ-1.509: the subK family, whose missing input was named three months ago

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-509/Probe509.agda`:

    subK-and : (TFacts's subK₁-and, at KValue's frame)

**and say whether the same argument serves the other five `subK` fields.** Land
nothing in `src/`.

**`[LJ-1.113]` NAMED THE MISSING INPUT AND NOBODY HAS TRIED IT SINCE.** Its row
18 reads: "`subValAt ... → y ∈ K` NEEDS NEW CONTENT: K closed under sub-values;
`subValAt-adequate` pins `pr (pr ar a) y ∈ T`, and **`arityK` closes it only with
`T ∈ K`**" (`agents/tasks/LJ-1-113/lj-1.113-report.md:48`). Row 19 says "same
closure" (`:49`). **So the whole family reduces to one membership, `T ∈ K`.**

**`arityK` IS NOW DELIVERED AT THESE INDICES AND IT WAS NOT WHEN THAT ROW WAS
WRITTEN.** `[LJ-1.495]` is GO: `KFacts` reaches `TFacts`'s frame by six
`KFactsCons` steps, and `arityK` (`src/L/Condensation.lagda.md:6114-6115`) is one
of the fields it carries. **`TFacts` does not state `arityK`**, so the shift
supplies something the record cannot say. **That is what makes this row payable
now and unpayable then.**

**A CHEAP CONFIRMATION FIRST, AND IT IS NOT THE OBLIGATION.** `transK`
(`src/L/Condensation/TwelveAgree.lagda.md:262-264`) is `arityK` with its two
arguments swapped, and **the tree already treats them as interchangeable**:
`arityK₀ N v hv hNK = transK v N hv hNK` at
`src/L/Coding/EnvSupply.lagda.md:436`. Confirm that and `transK` is paid for
nothing. Report it; do not count it as the obligation.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-509/Probe509.agda::subK-and"]

## SCOPE (write)
- agents/tasks/LJ-1-509/Probe509.agda
- agents/tasks/LJ-1-509/lj-1.509-report.md
- agents/tasks/LJ-1-509/review-of-subK-and.md
- agents/tasks/LJ-1-509/runs/

## PREMISES

1. `[LJ-1.113]` names `T ∈ K` as the missing input for this family. Basis: agents/tasks/LJ-1-113/lj-1.113-report.md:48
2. It says row 19 is the same closure. Basis: agents/tasks/LJ-1-113/lj-1.113-report.md:49
3. `subK₁-and` is stated over `subValAt` at a seven deep prefix. Basis: src/L/Condensation/TwelveAgree.lagda.md:265
4. `subK₀-and` is the sibling. Basis: src/L/Condensation/TwelveAgree.lagda.md:271
5. `transK` is `arityK` with the arguments swapped. Basis: src/L/Condensation/TwelveAgree.lagda.md:262
6. The tree already derives one from the other. Basis: src/L/Coding/EnvSupply.lagda.md:436
7. `arityK` is a `KFacts` field. Basis: src/L/Condensation.lagda.md:6114
8. `[LJ-1.495]` is GO and delivers `KFacts` at these indices. Basis: agents/tasks/LJ-1-495/lj-1.495-report.md:71
9. `[LJ-1.500]` is GO and shows the frame-hypothesis method at this record. Basis: agents/tasks/LJ-1-500/lj-1.500-report.md:145
10. `[LJ-1.506]` is GO and shows the refutation method at this record. Basis: agents/tasks/LJ-1-506/Probe506.agda:143
11. `KValue` binds the carrier and the stage. Basis: src/L/Condensation.lagda.md:7380
12. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
13. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
14. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**FORTY ONE OF FIFTY NINE POSITIONS ARE ACCOUNTED AND FIFTEEN REMAIN UNASKED.**
Three of the fifteen wait on `[LJ-1.508]`. **The `subK` family is six of the
other twelve**, and it is the only group in this record whose missing input a
previous dispatch has already named.

## WHAT IS MISSING

One membership, and whatever it takes to get it.

## THE REASONING

**D-10, BEFORE ANY AGDA.** `[LJ-1.113]` says `subValAt-adequate` pins
`pr (pr ar a) y ∈ T`. **Say at `file:line` what `T` IS in that reading and
whether anything at this frame gives `T ∈ K`.** If `T` is a bound variable of
the adequacy rather than a named set, say so and STOP: the row's own hint would
then be unusable and the family needs a different argument.

**IF THE BARE FORM IS FALSE, REFUTE IT.** `[LJ-1.506]` showed how at this record
(`agents/tasks/LJ-1-506/Probe506.agda:143-150`), and a machine-checked
counterexample with the weakest repairing hypothesis named is a full deliverable.

**TAKE THE WEAKEST HYPOTHESIS THAT WORKS AND DO NOT PIN A SLOT.** The
mathematician has ruled that way three times this day. A hypothesis that fixes
what occupies a slot would pre-empt `[LJ-1.505]` and will be refused.

**DO NOT USE A `TFacts` FIELD TO PROVE A `TFacts` FIELD**, and do not postulate.

**DO NOT TOUCH `valK`, `valV`, `valW` OR `wKfact`.** `[LJ-1.508]` holds the
first and asks about the other three.

**REQUIRED REPORT SECTION `## THE SIX subK FIELDS`.** One row per field
(`:265`, `:271`, `:277`, `:283`, `:290`, `:311`) saying whether this argument
serves it unchanged, serves it after a prefix change, or does not serve it.
**Do not build the other five.**

**REQUIRED REPORT SECTION `## transK`.** One line: whether it is `arityK`
swapped, with the `file:line` that settles it.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 170 lines in the probe, of which the obligation is
about 45. BASIS: `[LJ-1.500]` and `[LJ-1.506]` each rebuilt this frame in a
comparable file. Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is `T`, because the whole family turns on one membership and nobody has said
what set it is.

    -- what `subValAt-adequate` pins, with `T` named at file:line

**Do this FIRST, before any term, and write it into the report as you go.** If
`T` is not a set this frame can name, the family cannot be closed by
`[LJ-1.113]`'s route and the task stops at its cheapest point having retired a
three month old hint.

ESTIMATE for W3: about 20 lines and under 30 seconds. **Do not fund it against
`[LJ-1.506]`'s W3**: that opened a code set and this opens an adequacy.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO MAY PAY SIX POSITIONS FROM ONE ARGUMENT** and would confirm that
`[LJ-1.495]`'s shift is what unlocked a family that was priced as new content
before the shift existed.

**A NO-GO RETIRES `[LJ-1.113]`'s HINT FOR THIS FAMILY**, which is worth having:
that row has stood unchallenged and every later estimate of this record's cost
has rested on it.

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
  changed_files_none = ["agents/tasks/LJ-1-509/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-509/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-509/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-509/Probe509.agda"]
  changed_files_none = ["agents/tasks/LJ-1-509/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-509/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 220.594)
- CANDIDATE archive/dev/JOURNAL.md  (score 168.566)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 167.025)
- CANDIDATE dev/ARCHIVE.md  (score 149.340)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 134.667)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 61.753)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 55.502)
- CANDIDATE dev/literature/digest.md  (score 54.732)
- CANDIDATE dev/literature/terms-2026-08.md  (score 40.942)
- CANDIDATE dev/literature/devlin-errata.md  (score 31.169)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
