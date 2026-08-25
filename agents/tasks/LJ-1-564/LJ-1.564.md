# LJ-1.564: PowerIntoSucc, the direction nobody has attempted

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-564/Probe564.agda`:

    power-into-succ :
      (zf : ModelL.isZFModel) (κ δ : SL.S) → SuccCardL δ κ → InjL (𝒫 κ) δ

which is `PowerIntoSucc` (`agents/tasks/LJ-1-558/Probe558.agda:93-96`). Land
nothing in `src/`.

**`[LJ-1.558]` IS GO AND IT COLLAPSED THE JOIN FROM TEN INPUTS TO THREE.** Its
route to `GCHStatement` has three hypotheses and one module argument, and **the
list is empty of ambient facts** (`agents/tasks/LJ-1-558/lj-1.558-report.md`,
`## THE HYPOTHESES OF THE ROUTE`):

| # | hypothesis | state |
|---|---|---|
| 1 | `SuccCardExists` | **PAID** by `[LJ-1.528]` |
| 2 | `PowerIntoSucc` | **this brief** |
| 3 | `SuccIntoPower` | blocked on a formula |

**SO B5 IS OFF THE BILL.** The ambient cardinality fact `[LJ-1.550]` proved
`[LJ-1.523]`'s bridge needs was an artifact of THAT bridge and not of the
target.

**AND THIS ROW HAS NEVER BEEN ATTEMPTED.** Every dispatch this week went at
`SuccIntoPower`, its twin. **This is the direction the bounded subset theorem
was built for**: a constructible subset of κ lies in a stage below κ⁺
(`src/L/BoundedSubset.lagda.md:1621`), and the stage is counted.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-564/Probe564.agda::power-into-succ"]

## SCOPE (write)
- agents/tasks/LJ-1-564/Probe564.agda
- agents/tasks/LJ-1-564/lj-1.564-report.md
- agents/tasks/LJ-1-564/review-of-power-into-succ.md
- agents/tasks/LJ-1-564/runs/

## PREMISES

1. `[LJ-1.558]` is GO and its hypothesis list has no ambient fact. Basis: agents/tasks/LJ-1-558/lj-1.558-report.md:1
2. `PowerIntoSucc` is stated at its probe. Basis: agents/tasks/LJ-1-558/Probe558.agda:93
3. `SuccIntoPower` is the twin and is `GCHStatement`'s third conjunct. Basis: agents/tasks/LJ-1-558/Probe558.agda:99
4. `SuccCardExists` is paid. Basis: agents/tasks/LJ-1-528/Probe528.agda:638
5. `InjL` unfolds to a truncated `InjCode`. Basis: src/L/GCH.lagda.md:38
6. The bounded subset theorem puts a subset in a stage. Basis: src/L/BoundedSubset.lagda.md:1621
7. It sits under `levelIn` and `cover`. Basis: src/L/BoundedSubset.lagda.md:1555
8. `[LJ-1.543]` showed B6 does NOT need those two. Basis: agents/tasks/LJ-1-543/lj-1.543-report.md:1
9. `[LJ-1.559]` is GO and built `domAt`, the fourth `InjCode` conjunct. Basis: agents/tasks/LJ-1-559/lj-1.559-report.md:1
10. `[LJ-1.524]`, `[LJ-1.529]` and `[LJ-1.531]` built the other three. Basis: agents/tasks/LJ-1-524/lj-1.524-report.md:1
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. A stop is a deliverable. Basis: AGENTS.md:43
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

A bounded subset theorem under two hypotheses, and all four `InjCode` conjuncts
in four separate probes. **No term of this shape.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS WHETHER `levelIn` AND `cover` COME WITH IT.**
`src/L/BoundedSubset.lagda.md:1621` is the theorem and `:1555` carries the two
hypotheses. **Say at `file:line` whether this row needs the theorem at all, and
if it does, whether the two hypotheses are dischargeable here or must be
carried.** `[LJ-1.543]` found a sibling row did NOT need the theorem, so check
before you assume.

**IF THE TWO HYPOTHESES MUST BE CARRIED, CARRY THEM AND SAY SO.** Do not try to
discharge them: the archive prices them as a wall at 1.0k to 3.3k lines
(`archive/dev/LJ-dispatch-index.md:198`, `:222`), and **those are old prices at
an old tree that nothing may be funded against.** A row that lands under two
named hypotheses is a result; a row that stalls trying to kill them is not.

**THE FOUR `InjCode` CONJUNCTS ALL EXIST NOW.** `[LJ-1.559]` closed the last one.
**Say whether they apply at THIS pair**, `(𝒫 κ , δ)`, and if not, say what pair
they are at. `[LJ-1.566]` is assembling them and this brief does not.

**DO NOT ATTEMPT `SuccIntoPower`.** It is the twin, it is blocked on a formula,
and AD12 gives this brief one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## WHAT IT COST AND UNDER WHAT`.** The term, its
hypotheses in full, and a mark against any that is not discharged.

**REQUIRED REPORT SECTION `## HOW FAR GCHStatement NOW IS`.** Of `[LJ-1.558]`'s
three hypotheses, say how many are paid after this task and name what is left.
**Count, do not estimate.**

ESTIMATE: about 200 lines in the probe, of which the obligation is about 50.
BASIS: `[LJ-1.543]` and `[LJ-1.544]` built comparable rows against the same
chapter. **This estimate is uncertain because the row is unattempted.**
Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is whether `InjCode` can even be stated with `𝒫 κ` as its source.

    -- InjCode F (𝒫 κ) δ, at this frame, TYPE ONLY, no inhabitant

**Write it FIRST and typecheck it ALONE.** `[LJ-1.546]` asked the same question
for the other direction and the answer shaped the whole row. ESTIMATE: about 12
lines, under 60 seconds.

## WHAT GO AND NO-GO EACH EARN

**A GO LEAVES `GCHStatement` WANTING ONE TERM.** Two of three hypotheses would
be paid, and the campaign would have a single named target for the first time.

**A NO-GO THAT NAMES WHAT THIS DIRECTION WANTS IS WORTH AS MUCH**, because
nobody has ever measured it and every plan so far has assumed it is the easy
one.

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
  changed_files_none = ["agents/tasks/LJ-1-564/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-564/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-564/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-564/Probe564.agda"]
  changed_files_none = ["agents/tasks/LJ-1-564/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-564/review-of-*.md"]

[[branch]]
# PARK, NOT ESCALATE. MEASURED on LJ-1.534, 2026-08-22: this row matched
# a heap wall FOUR times, exit 251 each, to attempt_max. A critic
# re-runs the same probe and re-hits the same wall, so an escalation can only
# loop. **A heap wall is a resource fact and no critic can adjudicate it.**
id = "heap-wall-park"
priority = 30
action = "park_and_split"

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 161.717)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 149.048)
- CANDIDATE archive/dev/JOURNAL.md  (score 141.649)
- CANDIDATE dev/ARCHIVE.md  (score 126.981)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 117.851)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 44.653)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 42.758)
- CANDIDATE dev/literature/digest.md  (score 39.426)
- CANDIDATE dev/literature/geology.md  (score 34.529)
- CANDIDATE dev/literature/terms-2026-08.md  (score 30.944)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
