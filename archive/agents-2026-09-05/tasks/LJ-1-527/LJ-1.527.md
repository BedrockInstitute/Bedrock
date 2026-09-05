# LJ-1.527: row two of the chain, and the price of rows three to six

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-527/Probe527.agda`:

    body-unbounds : ⟨ γ ⊨ StepB.bodyB ⟩ → ⟨ γ ⊨ StepBody b f ⟩

**row two of the six-row chain `[LJ-1.525]` laid out.** Land nothing in `src/`.

**`[LJ-1.525]` IS GO AND IT DELIVERED ROW ONE AND THE WHOLE CHAIN.** Its
`## WHAT NOW CONSUMES THE CERTIFICATE` gives six rows between the leaf and
`LsetGraphAt`, each a transfer between a bounded formula and the machine's
formula at the same environment. **Row one is delivered by that task. Rows two
to six are not.**

**ROW TWO IS ONE CONGRUENCE AND I CHECKED IT MYSELF.** Put the two side by
side:

    bodyB    = (var 2 ∈̇ var (suc⁴ b)) ∧̇ ( appAt (suc⁴ f) 2 1
             ∧̇ ( leafB                 ∧̇ (var 3 ∈̇ var 0) ) )
    StepBody = (var 2 ∈̇ var (sh4 b))  ∧̇ ( appAt (sh4 f) 2 1
             ∧̇ ( DefAt zero (suc zero) ∧̇ (var 3 ∈̇ var 0) ) )

`src/L/Condensation.lagda.md:2404-2408` against
`src/L/Coding/Sequence.lagda.md:113-116`. **They differ in one slot: `leafB`
where `StepBody` has `DefAt zero (suc zero)`. That slot IS row one.**
`[LJ-1.525]` also reports that its section 6 proves the other three conjuncts
equal ON THE NOSE.

**SO THE OBLIGATION IS SMALL AND THE CENSUS IS THE REAL DELIVERABLE.** Say so
in your report if row two costs almost nothing; that is a true and useful
answer, not a thin one.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-527/Probe527.agda::body-unbounds"]

## SCOPE (write)
- agents/tasks/LJ-1-527/Probe527.agda
- agents/tasks/LJ-1-527/lj-1.527-report.md
- agents/tasks/LJ-1-527/review-of-body-unbounds.md
- agents/tasks/LJ-1-527/runs/

## PREMISES

1. `[LJ-1.525]` is GO and delivered row one. Basis: agents/tasks/LJ-1-525/lj-1.525-report.md:180
2. Its chain names six rows. Basis: agents/tasks/LJ-1-525/lj-1.525-report.md:197
3. `bodyB` is the bounded side. Basis: src/L/Condensation.lagda.md:2404
4. `StepBody` is the machine's side. Basis: src/L/Coding/Sequence.lagda.md:113
5. The differing slot is `DefAt`. Basis: src/L/Coding/Sequence.lagda.md:116
6. `leafB` is what stands there on the bounded side. Basis: src/L/Condensation.lagda.md:2398
7. `extAtB→extAt` is the delivered conversion row one used. Basis: src/L/Condensation.lagda.md:2514
8. `Σ₁-levelHood` is the certificate the chain would spend. Basis: src/L/BoundedSubset.lagda.md:145
9. `σ₁-up` is how a `Σ₁` certificate is spent. Basis: src/FOL/Absoluteness.lagda.md:182
10. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THE CONDENSATION LEG HAS A BILL WITH SIX ROWS AND ONE IS PAID.** Before
`[LJ-1.525]` it had a wall described in sentences. **That is the change worth
naming.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** `suc⁴ b` and `sh4 b` must be the same index. **Check
it at `file:line`.** If they are not, the two formulas differ in more than one
slot and the congruence is not one step.

**REBUILD ROW ONE, DO NOT IMPORT IT.** `[LJ-1.525]`'s term is probe-local.
Rebuild it at its delivered type and carry its five hypotheses into your
conclusion. **Do not discharge them and do not hide them.**

**DO NOT ATTEMPT ROWS THREE TO SIX.** AD12 gives this brief one obligation.
Row four alone is a second `extAtB→extAt` with the STEP's value in `K`, which
`[LJ-1.525]` calls a different and larger obligation than the leaf's.

**DO NOT SPEND THE CERTIFICATE.** The chain is not complete and a certificate
spent early proves nothing.

**DO NOT POSTULATE.**

**REQUIRED REPORT SECTION `## THE MEMBERSHIPS ROWS THREE TO SIX WANT`.** For
each of rows three, four, five and six, name every membership in `K` that its
transfer needs, as a type, and say whether the tree states it. **Use the same
three-way split `[LJ-1.523]` used: delivered in `src/`, delivered in a probe,
stated nowhere. This section is the deliverable and the obligation is not.**

**REQUIRED REPORT SECTION `## WHAT ROW TWO COST`.** In lines and seconds. **If
it is near zero, say the number.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 140 lines in the probe, of which the obligation is
about 20 and the rest is the rebuilt row one. BASIS: `[LJ-1.525]` built row one
and a six-row census in a comparable file. Comparables are of SHAPE and nothing
may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the index match, because the congruence is one step only if the two
formulas agree everywhere else.

    -- suc⁴ b against sh4 b, and suc⁴ f against sh4 f, as an equality

**Write it FIRST, and typecheck it ALONE.** If the indices do not match, the
row is not a congruence and the chain's second step is larger than
`[LJ-1.525]` priced it.

ESTIMATE for W3: about 10 lines and under 25 seconds. **Do not fund it against
`[LJ-1.525]`'s numbers**: that built a transfer and this compares two indices.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS ROW TWO AND PRICES THE REST**, which is what the leg needs more
than another term.

**A NO-GO AT THE INDICES SAYS THE CHAIN'S SECOND STEP WAS MISPRICED**, and the
remaining four rows must be re-read before any of them is ordered.

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
  # DELTA KEY ADDED 2026-08-22. Without it this row matches an acceptance
  # failure that delivered NOTHING, escalates, and matches again: MEASURED on
  # LJ-1.497, four times to attempt_max in six minutes, every one exit 1 with
  # delta 0. The row exists for the LJ-1.469 case, where the obligation WAS
  # delivered (delta -1) and acceptance failed. Keep it to that case.
  obligations_delta_max = -1
  changed_files_none = ["agents/tasks/LJ-1-527/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-527/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-527/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-527/Probe527.agda"]
  changed_files_none = ["agents/tasks/LJ-1-527/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-527/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 165.263)
- CANDIDATE archive/dev/JOURNAL.md  (score 145.766)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 142.762)
- CANDIDATE dev/ARCHIVE.md  (score 126.891)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 117.459)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 60.932)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 42.572)
- CANDIDATE dev/literature/digest.md  (score 32.905)
- CANDIDATE dev/literature/geology.md  (score 32.891)
- CANDIDATE dev/literature/terms-2026-08.md  (score 32.649)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
