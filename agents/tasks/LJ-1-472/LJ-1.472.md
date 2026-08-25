# LJ-1.472: does the condensation hull hold the numerals

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-472/Probe472.agda`:

    numerals-in-hull :
        (k : ℕ) → ⟨ fst (numeralL k) ∈ˢ H.T.Hull ⟩

where `H` is the definable hull the bounded-subset lemma builds at a limit
stage, exactly as `src/L/BoundedSubset.lagda.md:903-914` builds it. Land nothing
in `src/`.

**`[LJ-1.466]` MADE THIS THE QUESTION.** Its critic-upheld NO-GO measured that
every constant of the level formula is `numeralL k` for `k ∈ {0..11}`, and that
**none of those lies in a general hull carrier**
(`agents/tasks/LJ-1-466/lj-1.466-report.md:60`, committed `ec027e6`, condition
table under `## WHAT THE HULL MUST CONTAIN`). `levelIn` through the hull needs
those numerals to be hull members. **Nobody has asked whether they are.**

**READ THAT REPORT FIRST AND QUOTE ITS CONDITION TABLE.** If its verdict is not
a stated NO-GO, write nothing and stop.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-472/Probe472.agda::numerals-in-hull"]

## SCOPE (write)
- agents/tasks/LJ-1-472/Probe472.agda
- agents/tasks/LJ-1-472/lj-1.472-report.md
- agents/tasks/LJ-1-472/review-of-numerals-in-hull.md
- agents/tasks/LJ-1-472/runs/

## PREMISES

1. `[LJ-1.466]` is a critic-upheld NO-GO and it names this condition. Basis: agents/tasks/LJ-1-466/lj-1.466-report.md:60
2. Every constant of the level formula is a numeral. Basis: src/L/Coding/Sequence.lagda.md:349
3. `numeralL` is delivered. Basis: src/L/Axioms/Numerals.lagda.md:175
4. `base` needs a member of the hull's carrier. Basis: src/L/Hull.lagda.md:73
5. The hull is a term algebra closed under definable existence at the stage. Basis: src/L/Hull.lagda.md:120
6. Its members lie in the stage. Basis: src/L/Hull.lagda.md:330
7. The consumer builds the hull over `UK.X`, the union kit's set. Basis: src/L/BoundedSubset.lagda.md:903
8. `levelIn` is one of the two unpaid condensation hypotheses. Basis: src/L/BoundedSubset.lagda.md:917
9. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
10. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

`[LJ-1.466]` did the census: the constants are numerals and nothing else, and it
listed the condition per value. `[LJ-1.462]` built everything else on the hull
route: the packaging, `feed`, step 1, and steps 2 and 3 as types.

## WHAT IS MISSING

The membership. **Either the hull holds every numeral, in which case
`[LJ-1.466]`'s obligation reopens, or it does not, in which case the hull route
to `levelIn` is closed and the campaign should stop paying for it.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** Two routes, and the report must weigh both before a
term:

1. **By closure.** The hull is closed under definable existence
   (`src/L/Hull.lagda.md:120-123`). A numeral is definable without parameters,
   so `wit` at a formula naming `# k` should produce it. **Say whether that
   formula exists**; `[LJ-1.466]` found the constants but not a formula defining
   one.
2. **By the carrier.** The hull is built over `UK.X` and `base` lifts any member
   of it. **Say what `UK.X` contains**, at `file:line`.

**Name which route you took and why. If neither closes, say which is nearer.**

**THE SHAPE.** Rebuild the telescope down to the hull, copying
`src/L/BoundedSubset.lagda.md:903-914`. Do W3 first. Do not import a probe. Do
not build `levelIn` and do not build `lset-codes`.

**DO NOT ADD A HYPOTHESIS PUTTING A NUMERAL IN THE HULL BY FIAT.** If the hull
must be built over a larger `X`, that is a CONDITION ON THE CONSUMER and it
belongs in the report.

**REQUIRED REPORT SECTION `## WHAT THIS DECIDES`.** Say in two sentences what a
GO reopens and what a NO-GO closes. **A NO-GO here closes the hull route to
`levelIn` and the campaign should hear that plainly**, because `[LJ-1.451]`,
`[LJ-1.462]` and `[LJ-1.466]` have all spent dispatches on it.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 120 lines in the probe, of which the obligation is
about 20. BASIS: `agents/tasks/LJ-1-462/Probe462.agda` measured 63 non-blank
non-comment lines over 149 total rebuilding this same telescope. Comparables are
of SHAPE.

## W3, THE WIDEST UNMEASURED TERM

It is ONE numeral, not twelve.

    zero-in-hull : ⟨ fst (numeralL 0) ∈ˢ H.T.Hull ⟩

**Build it for `k = 0` alone, with the obligation omitted, and typecheck it.**
If one numeral cannot be placed, twelve cannot, and the route is closed at its
cheapest point. If it can, report by which of the two routes, because that
decides how the other eleven are priced.

ESTIMATE for W3: about 10 lines and under 15 seconds.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO REOPENS `[LJ-1.466]`'s OBLIGATION** and with it the hull route to
`levelIn`.

**A NO-GO CLOSES THAT ROUTE**, which is worth more: three tasks have now spent
dispatches on it, and a measured close redirects the condensation front instead
of funding a fourth.

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
  changed_files_none = ["agents/tasks/LJ-1-472/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-472/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-472-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-472/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-472/Probe472.agda"]
  changed_files_none = ["agents/tasks/LJ-1-472/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-472/review-of-*.md"]

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
