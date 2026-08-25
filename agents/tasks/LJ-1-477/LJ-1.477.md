# LJ-1.477: does the collapse commute with the stage operation

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-477/Probe477.agda`:

    piCommuteLset : (y : S) → ⟨ y ∈ˢ M ⟩ → C.π (Lset y) ≡ Lset (C.π y)

where `M` is the definable hull and `C = Collapse M`, exactly as
`src/L/BoundedSubset.lagda.md:903-916` builds them. Land nothing in `src/`.

**`[LJ-1.462]` STATED THIS AS A TYPE AND LEFT IT UNBUILT, AND IT IS STEP 4 OF
`levelIn`.** That critic-upheld NO-GO wrote `πCommuteLset` at
`agents/tasks/LJ-1-462/Probe462.agda:139-142` (committed `041135c`) and marked
it "Step 4. Absoluteness. Same type as πCommuteLset. Unbuilt."

**IT IS INDEPENDENT OF STEP 3.** `[LJ-1.474]` is building the code vector, which
is step 3. **This task must not touch that**, and a `levelIn` that joins the two
is a later brief.

**READ `[LJ-1.462]`'s REPORT FIRST** (verdict at `:75`). If its verdict is not a
stated NO-GO, or `πCommuteLset` is absent from its probe, write nothing and stop.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-477/Probe477.agda::piCommuteLset"]

## SCOPE (write)
- agents/tasks/LJ-1-477/Probe477.agda
- agents/tasks/LJ-1-477/lj-1.477-report.md
- agents/tasks/LJ-1-477/review-of-piCommuteLset.md
- agents/tasks/LJ-1-477/runs/

## PREMISES

1. `[LJ-1.462]` is a critic-upheld NO-GO and it states this type unbuilt. Basis: agents/tasks/LJ-1-462/lj-1.462-report.md:75
2. Its statement is at the probe that typechecked. Basis: agents/tasks/LJ-1-462/Probe462.agda:139
3. It is one of the four steps `levelIn` needs, and step 3 is a different task. Basis: agents/tasks/LJ-1-462/Probe462.agda:147
4. The collapse `π` is sealed and defined by `∈`-induction. Basis: src/V/Collapse.lagda.md:52
5. Its computation law is exported and the chapter spends it three times. Basis: src/V/Collapse.lagda.md:58
6. `π-member` reads a collapse value back to a carrier member. Basis: src/V/Collapse.lagda.md:63
7. The collapse is injective on the hull and its image is transitive. Basis: src/V/Collapse.lagda.md:214
8. `Lset` is a function on the L-structure's own carrier. Basis: src/L/Constructible.lagda.md:222
9. The hull's members lie in the stage. Basis: src/L/Hull.lagda.md:330
10. `levelIn` is one of the two unpaid condensation hypotheses. Basis: src/L/BoundedSubset.lagda.md:917
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

`[LJ-1.462]` inhabited step 1 (`Probe462.agda:133-134`) and stated steps 2 and 4
as types. `[LJ-1.472]` and `[LJ-1.474]` work step 3. **Step 4 has never been
attempted**, and it is the only one of the four that is an ABSOLUTENESS
statement rather than a definability one.

## WHAT IS MISSING

The commutation. Without it, even a complete step 3 does not give `levelIn`.

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT DECIDES WHETHER THIS IS PROVABLE OR FALSE.**
`π` is defined by `∈`-induction and its computation law is
`π x ≡ step x (λ y _ → π y)` (`src/V/Collapse.lagda.md:58-59`). `Lset` is defined
by its own recursion. **Commuting one past the other needs both laws to line up
at the same argument.** Write both computation laws out at `file:line` and say,
in one line, whether the collapse's `step` sends the members of `Lset y` to the
members of `Lset (π y)`.

**IF THE HULL IS NOT CLOSED UNDER `Lset`, THE STATEMENT IS ABOUT A `π` VALUE
OUTSIDE THE HULL AND THE TASK MUST SAY SO.** `[LJ-1.462]`'s step 2,
`HullClosedLset` (`Probe462.agda:136-138`), is exactly that closure and it is
also unbuilt. **This brief does NOT ask you to build it.** If step 4 cannot be
stated without step 2, say so and STOP: that dependency is a finding and it
changes the order of the remaining work.

**THE SHAPE.** Rebuild the telescope down to `C = Collapse M`, copying
`src/L/BoundedSubset.lagda.md:903-916` as `[LJ-1.462]` did. Take
`HullClosedLset` as a MODULE HYPOTHESIS if and only if the statement needs it,
and say plainly that you did. Do not import a probe.

**DO NOT BUILD `levelIn`, `lset-codes` OR `lset-code`.** One obligation.

**DO NOT POSTULATE, AND DO NOT ADD AN ABSOLUTENESS HYPOTHESIS.** Absoluteness of
`Lset` under the collapse is what this task measures; assuming it makes the
return worthless.

**REQUIRED REPORT SECTION `## WHAT LEVELIN STILL OWES`.** State, as types and at
`file:line`, which of `[LJ-1.462]`'s four steps are now built and which are not,
and price the join. **Do not claim `levelIn`.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 150 lines in the probe, of which the obligation is
about 40. BASIS: `agents/tasks/LJ-1-462/Probe462.agda` measured 63 non-blank
non-comment lines over 149 total rebuilding this same telescope and stating four
types. Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the two computation laws at one argument.

    both-compute : (y : S) → C.π (Lset y) ≡ _

**Apply `π-compute` at `Lset y` and typecheck THAT ALONE, with the obligation
omitted.** `π` is `opaque` and its law sits inside an `unfolding` block
(`src/V/Collapse.lagda.md:56-59`). **If the law cannot be spent at `Lset y`
without unfolding the seal, that is the finding**, and it is the heap-cost shape
`[LJ-1.398]` measured at 8 GB on a different seal. Report the wall time and peak
RSS for that step alone.

ESTIMATE for W3: about 10 lines and under 20 seconds. **If the seal opens, expect
far more and say so rather than pushing through.**

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO LEAVES `levelIn` A JOIN OF STATED PIECES**, with step 3 in `[LJ-1.474]`'s
hands and steps 1 and 4 built.

**A NO-GO SAYS THE COLLAPSE DOES NOT COMMUTE WITH THE STAGE OPERATION AT THIS
SITE**, which would close the hull route to `levelIn` for a reason no census
could have found, and redirect the condensation front.

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
# THE ACCEPTANCE ITSELF CAN FAIL, AND NOTHING IN THIS TEMPLATE USED TO MATCH IT.
# MEASURED 2026-08-21 on LJ-1.469: the term was GREEN and its ratio was 0.0055,
# well under the bar, but acceptance conjunct 4 FAILED and the run exited 1.
# Every branch keyed on exit 0 or 42 missed, so the task parked `no-match` with a
# delivered obligation. An acceptance failure is a real event and it routes to a
# critic rather than to silence.
id = "accept-failed"
priority = 14
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 1
  changed_files_none = ["agents/tasks/LJ-1-477/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-477/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-477-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-477/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-477/Probe477.agda"]
  changed_files_none = ["agents/tasks/LJ-1-477/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-477/review-of-*.md"]

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
