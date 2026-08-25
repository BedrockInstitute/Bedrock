# LJ-1.463: someEnv again, on the frame that now transfers

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-463/Probe463.agda`:

    someEnv-at-K : someEnvDef {9} iK' Kenv'

where `someEnvDef` is `src/L/Condensation/LowerAgree.lagda.md:52-58` and `Kenv'`,
`iK'` are the RE-LAID-OUT frame `[LJ-1.457]` delivered. Land nothing in `src/`.

**THIS OBLIGATION RAN ONCE AND DIED ON A LAYOUT THAT IS NOW FIXED.**
`[LJ-1.450]` met `[UnequalTerms] 14 != 8` transferring the 24 fields the two
records share, and its critic upheld the stop. `[LJ-1.457]` is GO on exactly
that transfer (`agents/tasks/LJ-1-457/lj-1.457-report.md:87`, committed
`bc87884`, term at `agents/tasks/LJ-1-457/Probe457.agda:136-167`).

**READ `[LJ-1.457]`'s REPORT FIRST AND TAKE THE LAYOUT FROM ITS PROBE, NEVER FROM
ITS BRIEF OR FROM MINE.** If its verdict is not `GO`, write nothing and stop.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-463/Probe463.agda::someEnv-at-K"]

## SCOPE (write)
- agents/tasks/LJ-1-463/Probe463.agda
- agents/tasks/LJ-1-463/lj-1.463-report.md
- agents/tasks/LJ-1-463/review-of-someEnv-at-K.md
- agents/tasks/LJ-1-463/runs/

## PREMISES

1. `[LJ-1.457]` is GO on the 24-field prefix at a re-laid-out frame. Basis: agents/tasks/LJ-1-457/lj-1.457-report.md:87
2. Its delivered term is at the probe that typechecked. Basis: agents/tasks/LJ-1-457/Probe457.agda:136
3. `someEnv` is a field of `TFacts`. Basis: src/L/Condensation/TwelveAgree.lagda.md:289
4. `TFacts` has 55 fields and no inhabitant. Basis: src/L/Condensation/TwelveAgree.lagda.md:129
5. `someEnvDef` is stated in the lower agreement. Basis: src/L/Condensation/LowerAgree.lagda.md:52
6. `[LJ-1.113]` names `someEnv` as THE widest unmeasured term of the 28, the only construction among them, and names the probe. Basis: agents/tasks/LJ-1-113/lj-1.113-report.md:147
7. It prices the whole 28 at about 250 lines and calls the figure a hypothesis. Basis: agents/tasks/LJ-1-113/lj-1.113-report.md:135
8. The other 25 are closures of one shape and 2 are slot equalities the consumer supplies. Basis: agents/tasks/LJ-1-113/lj-1.113-report.md:61
9. `KValue` supplies the bound's closure facts the construction will spend. Basis: src/L/Condensation.lagda.md:7415
10. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
11. A measured cure does not transfer by analogy. Basis: dev/LESSONS.md:3752
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THE LAYOUT WALL IS DOWN.** `[LJ-1.457]` transferred the 24 fields `KFacts`
already supplies onto a frame `TFacts` can address. That was the break
`[LJ-1.450]` measured, and it was a layout and not the mathematics.

**AND `[LJ-1.113]` DID THE CLASSIFICATION YEARS OF DISPATCHES AGO.** 28 facts
need new content, 1 is derivable, 0 unknown, and the report names a supplier for
each.

## WHAT IS MISSING

The one field of the 28 that is a construction rather than a closure.

## THE REASONING

**WHY THIS FIELD FIRST.** `[LJ-1.113]` split the 28 into three shapes: 25
satisfier-in-K closures, 2 slot equalities, and 1 environment-existence
construction. **The 25 share a pattern and the 1 does not.** If the construction
fails, the 250-line price fails with it whatever the 25 cost.

**D-10, BEFORE ANY AGDA.** Quote `someEnvDef` in full and quote `[LJ-1.457]`'s
`Kenv'` and its index names. **Say in one line that the arity `[LJ-1.457]`
settled is the arity `someEnvDef` needs, and give the evidence.** If the two
differ, name the difference and STOP.

**THE SHAPE.** Import `L.Condensation` and `L.Condensation.LowerAgree` from
`src/`. Rebuild `[LJ-1.457]`'s frame at its delivered layout; do not import a
probe and do not re-derive the arithmetic. Do W3 first. Build the construction
from the model's own environment constructors and the bound's closure facts.

**DO NOT BUILD THE OTHER 27 AND DO NOT WRITE A `TFacts` RECORD.** One field.

**DO NOT POSTULATE AND DO NOT ADD A HYPOTHESIS TO CLOSE IT.**

**REQUIRED REPORT SECTION `## WHAT THE 27 NOW COST`.** You will have measured one
of them. Give the measured line count and wall time, say whether
`[LJ-1.113]`'s 250-line figure still stands, and **do NOT re-price the 25
closures from this one construction**: they are a different shape and C-42
forbids the transfer.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 150 lines in the probe, of which the obligation is
about 45. BASIS: `[LJ-1.457]`'s own probe runs about 170 lines for the frame plus
24 field transfers, and this file rebuilds that frame and adds one construction.
Comparables are of SHAPE.

## W3, THE WIDEST UNMEASURED TERM

It is whether the environment the construction must build can be shown to lie in
`K` at all.

    env-in-K : (ya yc ar : S) → ⟨ fst ya ∈ fst K ⟩ → ⟨ fst yc ∈ fst K ⟩
             → ⟨ fst ar ∈ fst K ⟩ → Σ[ E ∈ S ] ⟨ fst E ∈ fst K ⟩

**Write that membership half FIRST, without the satisfaction half, and typecheck
it ALONE.** `[LJ-1.113]` says the machine's environment machinery describes
environments and does not build one from `K` memberships
(`lj-1.113-report.md:152-155`). **If the membership half cannot be built, the
satisfaction half is unreachable and the task stops at its cheapest point.**

ESTIMATE for W3: about 20 lines and under 15 seconds. BASIS: `KValue`'s own
closure facts are one line each (`src/L/Condensation.lagda.md:7415-7425`).

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO PUTS THE FIRST OF `[LJ-1.113]`'s 28 IN THE TREE** and turns a five-year-old
classification into work a brief can order.

**A NO-GO NAMES WHAT THE ENVIRONMENT CONSTRUCTION STILL NEEDS**, which is the one
piece `[LJ-1.113]` could not price from the record alone.

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
  changed_files_any = ["agents/tasks/LJ-1-463/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-463-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-463/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-463/Probe463.agda"]
  changed_files_none = ["agents/tasks/LJ-1-463/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-463/review-of-*.md"]

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
