# LJ-1.550: is B5 needed at all, when the target crosses no ambient boundary

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-550/Probe550.agda`:

    bridge-without-B5 : <the bridge's conclusion, from the NINE other inputs>

the same implication `[LJ-1.523]` priced, with `AmbientSpentAtSucc` **REMOVED
from the hypotheses**. Land nothing in `src/`.

**IF IT WILL NOT BUILD, the deliverable is the site where B5 is really used**,
stated as a term whose type names B5 and nothing else, plus the report section
below. **A refutation of this brief's premise is a full result.**

**WHY I THINK B5 MAY NOT BELONG ON THE LIST, AND IT IS A TYPE ARGUMENT.** B5 is
`AmbientSpentAtSucc`, whose payload is `CardSpentAt (fst δ) (fst κ)`, and that
unfolds to `⟪ δ ⟫ ↪ ⟪ κ ⟫ → Empty.⊥` (`agents/tasks/LJ-1-523/Probe523.agda:214`):
**an AMBIENT injection, at the V-carrier, must not exist.** But the target
statement is internal all the way down. `GCHStatement`
(`src/L/GCH.lagda.md:59-68`) asks only for `SuccCardL δ κ`, `InjL (𝒫 κ) δ` and
`InjL δ (𝒫 κ)`, and `InjL` is a truncated `InjCode`
(`src/L/GCH.lagda.md:38`), which is satisfaction of three formulas plus a
value clause (`src/L/Cardinal.lagda.md:224-228`). **The chapter says so in its
own words at `src/L/GCH.lagda.md:57-58`: "no ambient function type crosses the
⊨ boundary."**

**AND THE MATHEMATICS SAYS THE SAME THING.** δ is a cardinal OF L. Nothing makes
it a cardinal of V, and an ambient injection `⟪ δ ⟫ ↪ ⟪ κ ⟫` may exist while δ
is still L's successor cardinal to κ. **So B5 is not merely unpaid: it may be
UNPROVABLE as stated, and a bridge that needs it would be a bridge nobody can
inhabit.** That is what this task settles.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-550/Probe550.agda::bridge-without-B5"]

## SCOPE (write)
- agents/tasks/LJ-1-550/Probe550.agda
- agents/tasks/LJ-1-550/lj-1.550-report.md
- agents/tasks/LJ-1-550/review-of-bridge-without-B5.md
- agents/tasks/LJ-1-550/runs/

## PREMISES

1. B5's type is stated in `[LJ-1.523]`'s probe. Basis: agents/tasks/LJ-1-523/Probe523.agda:219
2. Its payload is a non-existence of an AMBIENT injection. Basis: agents/tasks/LJ-1-523/Probe523.agda:214
3. `[LJ-1.544]` counted B5 UNPAID and stated nowhere. Basis: agents/tasks/LJ-1-544/lj-1.544-report.md:1
4. `GCHStatement` asks for three things and no ambient one. Basis: src/L/GCH.lagda.md:59
5. The chapter states that no ambient function type crosses the boundary. Basis: src/L/GCH.lagda.md:57
6. `InjL` is a truncated `InjCode`. Basis: src/L/GCH.lagda.md:38
7. `InjCode` is satisfaction of three formulas plus a value clause. Basis: src/L/Cardinal.lagda.md:223
8. `IsCardinalL` is itself stated by `InjCode`, not ambiently. Basis: src/L/Cardinal.lagda.md:230
9. `[LJ-1.523]` priced the bridge and found the type forms with no holes. Basis: agents/tasks/LJ-1-523/lj-1.523-report.md:1
10. `[LJ-1.526]` overturned an archived claim about `IsCardinal` by measurement. Basis: agents/tasks/LJ-1-526/lj-1.526-report.md:1
11. A stop is a deliverable. Basis: AGENTS.md:43
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

`[LJ-1.523]`'s bridge type, which forms with no holes, and seven of its ten
inputs paid.

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE USE SITE.** Read `[LJ-1.523]`'s probe and
say at `file:line` **every place `AmbientSpentAtSucc` is consumed.** If it is
consumed nowhere, say so and the obligation is nearly free. If it is consumed,
name the step and say what that step needs it FOR.

**DO NOT TRY TO PROVE B5 AND DO NOT TRY TO REFUTE B5.** Both are the wrong
target. Whether an ambient injection exists is not settled inside this
development, and a task that tries will spend its estimate on a question the
tree cannot answer. **The obligation is the bridge WITHOUT it.**

**IF B5 IS GENUINELY LOAD-BEARING, THAT IS THE RESULT.** Say which conclusion
fails without it, and say whether the conclusion that fails is one
`GCHStatement` actually asks for, or one `[LJ-1.523]` added on the way. **Those
are different, and the difference is the whole value of this task.**

**DO NOT RESTATE `[LJ-1.523]`'S BRIDGE MORE WEAKLY TO MAKE IT GO THROUGH.** If
you change any other hypothesis, the result is about a different bridge and
says nothing. Change exactly one thing: remove B5.

**DO NOT BUILD B9 OR B10.** They stay as hypotheses here. AD12 gives this brief
one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## WHERE B5 IS USED`.** Every consumption site at
`file:line`, or the sentence that there are none.

**REQUIRED REPORT SECTION `## WHAT THE JOIN NOW STANDS AT`.** Count the ten
inputs and name the unpaid ones. **If B5 comes off the list, say the join has
NINE inputs and not ten, and say who ruled it off.**

ESTIMATE: about 110 lines in the probe, of which the obligation is about 20.
BASIS: `[LJ-1.523]` built the whole bridge type at a comparable size and this
rebuilds one implication of it. Comparables are of SHAPE and nothing may be
funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is whether `[LJ-1.523]`'s bridge consumes B5 anywhere at all.

    -- the bridge's conclusion, with AmbientSpentAtSucc bound but UNUSED,
    -- typechecked with an unused-variable check on

**Write it FIRST and typecheck it ALONE.** If the elaborator accepts the term
with B5 unused, the answer is already in hand and the rest is bookkeeping.
ESTIMATE: about 15 lines, under 60 seconds.

## WHAT GO AND NO-GO EACH EARN

**A GO REMOVES A WHOLE INPUT FROM THE JOIN, AND IT REMOVES THE ONLY ONE THAT
ASKS FOR SOMETHING OUTSIDE L.** The join would stand at eight of nine, with
only B9 and B10 left, and both of those have named routes.

**A NO-GO SAYS THE BRIDGE AS STATED NEEDS AN AMBIENT CARDINALITY FACT**, which
is a stop worth declaring at once: it would mean `[LJ-1.523]`'s bridge is the
wrong bridge and the mathematician must restate it against `GCHStatement`
directly.

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
  changed_files_none = ["agents/tasks/LJ-1-550/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-550/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-550/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-550/Probe550.agda"]
  changed_files_none = ["agents/tasks/LJ-1-550/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-550/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 212.684)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 188.835)
- CANDIDATE archive/dev/JOURNAL.md  (score 181.784)
- CANDIDATE dev/ARCHIVE.md  (score 146.670)
- CANDIDATE archive/dev/DD-archived.md  (score 139.979)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 75.570)
- CANDIDATE dev/literature/devlin-II5.md  (score 62.075)
- CANDIDATE dev/literature/digest.md  (score 46.598)
- CANDIDATE dev/literature/geology.md  (score 37.731)
- CANDIDATE dev/literature/terms-2026-08.md  (score 36.983)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
