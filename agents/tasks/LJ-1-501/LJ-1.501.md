# LJ-1.501: two tag equations that pay four fields

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-501/Probe501.agda`:

    tagEq-at-t : (k : ℕ) (t : Fin (5 + n))
               → (whatever this frame gives about the layout)
               → fst (lookup (suc (suc (suc (suc (suc (suc t)))))) γ') ≡ fst (numeralL k)

**the tag equation at the two extra indices `t0` and `t1`, generic in the tag.**
`t0eq` and `t1eq` are its two instances. Land nothing in `src/`.

**ONE OBLIGATION PAYS FOUR FIELDS, AND I MEASURED WHY.** `TFacts` states four
fields this brief is about: `t0eq` (`src/L/Condensation/TwelveAgree.lagda.md:181`),
`t1eq` (`:182`), `t0K` (`:183-184`) and `num1K` (`:185`). Two of the four are
free once you have the other two:

1. **`num1K` IS `numK1`.** `TFacts.num1K` at `:185` and `TFacts.numK1` at `:146`
   have the SAME type, character for character:
   `⟨ fst (numeralL 1) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩`.
   And `numK1` is one of the twenty-six that `[LJ-1.495]` delivered
   (`agents/tasks/LJ-1-495/Probe495.agda:166-199`, GO). **So `num1K` costs
   nothing.** Report that as a finding; do not treat it as a defect I have ruled.

2. **`t0K` IS A TRANSPORT.** `[LJ-1.113]` MEASURED it: "`t0K` is provable from
   `t0eq` plus the delivered `KFacts.numK0`"
   (`agents/tasks/LJ-1-113/lj-1.113-report.md:130-131`), by transporting `t0eq`
   into the `numK0` field (`:128`). `numK0` is also one of `[LJ-1.495]`'s
   twenty-six.

**SO THE ONLY UNPAID THING IS THE TAG EQUATION ITSELF**, and `KFacts` cannot
supply it, because `KFacts` has no `t0` and no `t1` index
(`src/L/Condensation.lagda.md:6079`). It must come from the frame's layout.

**BUILD AT `KValue`'s FRAME.** `[LJ-1.496]` measured that the `PropAgree` chain
binds no stage (`agents/tasks/LJ-1-496/lj-1.496-report.md:78-82`) and the
mathematician has ruled that this front specializes at `KValue`
(`src/L/Condensation.lagda.md:7380-7383`).

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-501/Probe501.agda::tagEq-at-t"]

## SCOPE (write)
- agents/tasks/LJ-1-501/Probe501.agda
- agents/tasks/LJ-1-501/lj-1.501-report.md
- agents/tasks/LJ-1-501/review-of-tagEq-at-t.md
- agents/tasks/LJ-1-501/runs/

## PREMISES

1. `t0eq` is a tag equation at the extra index `t0`. Basis: src/L/Condensation/TwelveAgree.lagda.md:181
2. `t1eq` is the same at `t1`. Basis: src/L/Condensation/TwelveAgree.lagda.md:182
3. `t0K` is a membership at that same index. Basis: src/L/Condensation/TwelveAgree.lagda.md:183
4. `num1K` states the numeral one is in `K`. Basis: src/L/Condensation/TwelveAgree.lagda.md:185
5. `numK1` states the same thing at the same indices. Basis: src/L/Condensation/TwelveAgree.lagda.md:146
6. `[LJ-1.113]` measured that `t0K` follows from `t0eq` and `numK0`. Basis: agents/tasks/LJ-1-113/lj-1.113-report.md:130
7. Its method was a transport of `t0eq` into the delivered field. Basis: agents/tasks/LJ-1-113/lj-1.113-report.md:128
8. `[LJ-1.495]` is GO and delivers `numK0` and `numK1` at these indices. Basis: agents/tasks/LJ-1-495/lj-1.495-report.md:71
9. `KFacts` has no `t0` or `t1` index, so the shift cannot supply the tag equation. Basis: src/L/Condensation.lagda.md:6079
10. `KValue` is the module that binds the carrier. Basis: src/L/Condensation.lagda.md:7380
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

`[LJ-1.495]` paid twenty-six fields. `[LJ-1.113]` measured one reduction and
never built the term it needed. **This task builds that one thing.**

## WHAT IS MISSING

The layout fact, and nothing else.

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE WHOLE RISK.** `t0` and `t1` are
PARAMETERS of `TFacts`, not fixed slots. Nothing in the record says what sits at
them. **Say at `file:line` what determines the layout at `KValue`'s frame**, and
whether `numeralL 0` provably sits at slot `t0` there. **If nothing determines
it, STOP AND SAY SO**: the tag equation would then be a HYPOTHESIS the frame must
take, not a fact it can prove, and that is a statement about the record's design
that no dispatch has made.

**A STOP HERE IS THE MORE VALUABLE OUTCOME AND YOU SHOULD NOT AVOID IT.** If the
layout is free, then `TFacts` cannot be inhabited at any frame without a layout
hypothesis, and every remaining field brief on this front has to carry one.

**CONFIRM THE TWO FREE FIELDS BEFORE YOU BUILD ANYTHING.** Typecheck that
`num1K`'s type and `numK1`'s type are the same, and that `t0K` transports. **Both
are cheap and both are reported whatever happens to the obligation.**

**DO NOT BUILD A `TFacts` VALUE.** Fifty-five fields are out of scope and AD12
gives this brief one obligation. **Do not attempt the `envK-*` family or the code
readers**: `[LJ-1.499]` and `[LJ-1.500]` hold those and are running.

**REQUIRED REPORT SECTION `## THE FOUR FIELDS, ACCOUNTED`.** One row per field
with its `file:line` and its state: paid by this task, free from `[LJ-1.495]`,
free by transport, or unpaid with the reason. **Do not price the other
fifty-five.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 130 lines in the probe, of which the obligation is
about 25. BASIS: `[LJ-1.495]` rebuilt this frame and read fields off a shift in a
comparable file. Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the layout at `t0`, because `t0` is a parameter and no dispatch has ever
asked what fixes it.

    layout-at-t0 : (what the frame gives) → fst (lookup (suc⁶ t0) γ') ≡ fst (numeralL 0)

**Write it FIRST, with the obligation omitted, and typecheck it ALONE.** This is
the whole question: if it forms, the generic version is one abstraction away and
three more fields fall out; if it does not, the finding is that the record needs
a layout hypothesis and the task stops at its cheapest point.

ESTIMATE for W3: about 20 lines and under 30 seconds. **Do not fund it against
`[LJ-1.495]`'s 2.44 s**: that measured a record shift and this measures a slot.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS FOUR FIELDS FOR ONE TERM** and brings the accounted total on this
record to thirty of fifty-nine.

**A NO-GO SAYS `TFacts` CANNOT BE INHABITED WITHOUT A LAYOUT HYPOTHESIS**, which
would be a statement about the record's design rather than about one field, and
every remaining brief on this front would have to carry it.

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
  changed_files_none = ["agents/tasks/LJ-1-501/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-501/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-501/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-501/Probe501.agda"]
  changed_files_none = ["agents/tasks/LJ-1-501/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-501/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 191.896)
- CANDIDATE archive/dev/JOURNAL.md  (score 158.535)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 149.424)
- CANDIDATE dev/ARCHIVE.md  (score 136.828)
- CANDIDATE archive/dev/PLAN-archived.md  (score 123.491)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 64.753)
- CANDIDATE dev/literature/devlin-II5.md  (score 45.576)
- CANDIDATE dev/literature/terms-2026-08.md  (score 38.286)
- CANDIDATE dev/literature/digest.md  (score 34.461)
- CANDIDATE dev/literature/geology.md  (score 32.841)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
