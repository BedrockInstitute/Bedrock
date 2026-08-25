# LJ-1.481: step two, from the codes step three just built

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-481/Probe481.agda`:

    HullClosedLset : (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ Lset y ∈ˢ M ⟩

where `M` is the definable hull, exactly as `src/L/BoundedSubset.lagda.md:903-914`
builds it. Land nothing in `src/`.

**`[LJ-1.462]` NUMBERED FOUR STEPS FOR `levelIn` AND THIS IS THE ONE NOBODY HAS
TRIED.** Step 1 is built (`Probe462.agda:133-134`). Step 3 is GO: `[LJ-1.474]`
inhabits `lset-codes` (`agents/tasks/LJ-1-474/Probe474.agda:124-125`, committed
`57cfb7a`). Step 4 is a critic-upheld NO-GO on the computation-law route
(`[LJ-1.477]`). **Step 2 is `HullClosedLset`, stated at
`agents/tasks/LJ-1-462/Probe462.agda:136-138` and never attempted.**

**AND STEP 3 IS VERY LIKELY ITS PROOF.** A `Code` whose value is `Lset y` puts
`Lset y` in the hull by `inHull` (`src/L/Hull.lagda.md:117-118`), which is one
line. **Feed `lset-codes` to `wit` at the packaged level formula, then apply
`inHull`.**

**READ `[LJ-1.474]` AND `[LJ-1.462]` FIRST.** If 474's verdict is not `GO`, write
nothing and stop.

**THIS OBLIGATION RAN ONCE AND THE WORKER WROTE NOTHING.** `[LJ-1.479]` parked
with `no-change` (`dev/pod/transitions/2026-08.jsonl:1568`): no report, no probe,
no obstruction file. **That is not a mathematical result and there is nothing to
inherit from it.** Do not read its task home and do not cite it.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-481/Probe481.agda::HullClosedLset"]

## SCOPE (write)
- agents/tasks/LJ-1-481/Probe481.agda
- agents/tasks/LJ-1-481/lj-1.481-report.md
- agents/tasks/LJ-1-481/review-of-HullClosedLset.md
- agents/tasks/LJ-1-481/runs/

## PREMISES

1. `[LJ-1.474]` is GO on `lset-codes`. Basis: agents/tasks/LJ-1-474/lj-1.474-report.md:70
2. Its delivered term is at the probe that typechecked. Basis: agents/tasks/LJ-1-474/Probe474.agda:124
3. `[LJ-1.462]` states step 2 as a type and leaves it unbuilt. Basis: agents/tasks/LJ-1-462/Probe462.agda:136
4. It also built `feed`, `wit` applied to the packaged level formula. Basis: agents/tasks/LJ-1-462/Probe462.agda:101
5. `inHull` puts a code's value in the hull, in one line. Basis: src/L/Hull.lagda.md:117
6. `wit` builds a code from a formula and a vector of earlier codes. Basis: src/L/Hull.lagda.md:73
7. `[LJ-1.472]` is GO on the numerals being hull members. Basis: agents/tasks/LJ-1-472/lj-1.472-report.md:151
8. `[LJ-1.477]` is a critic-upheld NO-GO on step 4 by the computation-law route. Basis: agents/tasks/LJ-1-477/lj-1.477-report.md:97
9. `levelIn` is one of the two unpaid condensation hypotheses. Basis: src/L/BoundedSubset.lagda.md:917
10. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
11. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

Three of the four pieces this needs: the packaged formula and `feed`
(`[LJ-1.462]`), the code vector (`[LJ-1.474]`), and `inHull` in the chapter.

## WHAT IS MISSING

The join, and the one thing it may not have: **the code `wit` builds must have
`Lset y` as its VALUE, and nobody has checked that the level formula's witness is
that set rather than some other satisfier.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE WHOLE RISK.** `wit k ψ vs` is the WITNESS
of a satisfiable formula (`src/L/Hull.lagda.md:73-74`, and `search` at `:126`).
**A witness is a set that satisfies ψ; it is `Lset y` only if ψ pins it
uniquely.** `[LJ-1.458]` found the delivered adequacy `Lset-only` at
`src/L/Hierarchy.lagda.md:334-335` and reported that it carries an extra
`IsOrd`. **Say, at `file:line`, whether `Lset-only` gives uniqueness and where
the `IsOrd` comes from at a hull member `y`.** If it does not, the witness is not
`Lset y` and the obligation is a NO-GO whatever the codes do.

**THE SHAPE.** Rebuild `[LJ-1.462]`'s telescope down to the hull, copying
`src/L/BoundedSubset.lagda.md:903-914`. Rebuild `[LJ-1.474]`'s `lset-codes`. Feed
them to `wit`. Apply `inHull`. Do not import a probe.

**DO NOT BUILD `levelIn` AND DO NOT TOUCH STEP 4.** `[LJ-1.477]` measured that
route and its NO-GO stands.

**DO NOT POSTULATE AND DO NOT ADD AN ORDINALITY HYPOTHESIS ON `y`.** The hull
carries none, and adding one changes the statement `levelIn` needs.

**REQUIRED REPORT SECTION `## WHAT LEVELIN STILL OWES`.** State which of the four
steps are now built, as types and at `file:line`, and say plainly that step 4 is
a critic-upheld NO-GO. **Do not claim `levelIn`.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 150 lines in the probe, of which the obligation is
about 25. BASIS: `[LJ-1.474]` rebuilt this same telescope and its codes; the join
adds `wit` and `inHull`, which are two applications. Comparables are of SHAPE.

## W3, THE WIDEST UNMEASURED TERM

It is uniqueness, not the codes.

    pins : the level formula has at most one satisfier at a given index

**State that as a type from `Lset-only` (`src/L/Hierarchy.lagda.md:334-335`) and
typecheck it ALONE, with the obligation omitted.** `[LJ-1.458]` reported the
extra `IsOrd`; **source it at a hull member or report that it has no source.**
If uniqueness fails, `wit`'s value need not be `Lset y` and the task stops at its
cheapest point.

ESTIMATE for W3: about 12 lines and under 15 seconds.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO LEAVES `levelIn` OWING ONLY STEP 4**, which `[LJ-1.477]` has already
measured as closed on one route, so the next question is whether a second route
exists.

**A NO-GO SAYS THE WITNESS IS NOT THE SET**, which would mean `[LJ-1.474]`'s
codes buy less than they look and the hull route needs uniqueness before
anything else.

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
  changed_files_none = ["agents/tasks/LJ-1-481/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-481/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-481-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-481/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-481/Probe481.agda"]
  changed_files_none = ["agents/tasks/LJ-1-481/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-481/review-of-*.md"]

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
