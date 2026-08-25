# LJ-1.558: a route to GCHStatement that never lands inside Lset δ

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-558/Probe558.agda`:

    gch-route-without-stage :
      <GCHStatement's conclusion, from hypotheses NONE of which is an
       ambient cardinality fact, and by a derivation that never lands a
       conclusion inside `Lset (fst δ)`>

You may take `InjL (𝒫 κ) δ` and `InjL δ (𝒫 κ)` themselves as hypotheses: the
task is the ROUTE, not those two injections. Land nothing in `src/`.

**`[LJ-1.550]` IS A NO-GO, UPHELD, AND ITS REASON IS NARROWER THAN ITS
VERDICT.** It proved the bridge cannot drop B5, and `site-forced`
(`agents/tasks/LJ-1-550/Probe550.agda:385-389`) says why: any ambient cardinal
μ above κ is an L-cardinal by readback (`src/L/CantorBernstein.lagda.md:33-38`),
so `SuccCardL`'s leastness gives δ ≤ μ; **and "landing the conclusion inside
`Lset (fst δ)` needs μ ≤ δ", so μ ≡ δ and the ambient hypothesis cannot be
moved off the successor.**

**READ THAT CONDITIONAL.** The forcing enters through **landing the conclusion
inside `Lset (fst δ)`**. That is a step of `[LJ-1.523]`'s bridge. **It is NOT
something `GCHStatement` asks for**: the target names `SuccCardL δ κ`,
`InjL (𝒫 κ) δ` and `InjL δ (𝒫 κ)` and nothing else
(`src/L/GCH.lagda.md:59-68`), and the chapter states at `:57-58` that **"no
ambient function type crosses the ⊨ boundary."**

**SO THE QUESTION THIS TASK SETTLES IS WHETHER THE STAGE LANDING IS FORCED BY
THE TARGET OR ONLY BY ONE BRIDGE.** `[LJ-1.550]` confirmed my premise and
refuted my conclusion; this brief asks the version of the question that its
measurement leaves open, and I say plainly that it is the second attempt.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-558/Probe558.agda::gch-route-without-stage"]

## SCOPE (write)
- agents/tasks/LJ-1-558/Probe558.agda
- agents/tasks/LJ-1-558/lj-1.558-report.md
- agents/tasks/LJ-1-558/review-of-gch-route.md
- agents/tasks/LJ-1-558/runs/

## PREMISES

1. `[LJ-1.550]` is a NO-GO and its critic upheld it. Basis: agents/tasks/LJ-1-550/review-of-bridge-without-B5.md:1
2. Its one sentence names the ambient fact at δ. Basis: agents/tasks/LJ-1-550/review-of-bridge-without-B5.md:21
3. `site-forced` conditions the forcing on the stage landing. Basis: agents/tasks/LJ-1-550/Probe550.agda:385
4. It agrees `GCHStatement` names no ambient type. Basis: agents/tasks/LJ-1-550/review-of-bridge-without-B5.md:26
5. Readback makes an ambient cardinal an L-cardinal. Basis: src/L/CantorBernstein.lagda.md:33
6. `GCHStatement` asks for three things. Basis: src/L/GCH.lagda.md:59
7. The chapter says no ambient function type crosses the boundary. Basis: src/L/GCH.lagda.md:57
8. `SuccCardL`'s fourth component is a leastness clause. Basis: src/L/GCH.lagda.md:47
9. B1 is paid in the trophy case. Basis: src/Landmarks.lagda.md:76
10. B2 and B3 are paid in `CantorBernstein`. Basis: src/L/CantorBernstein.lagda.md:51
11. A stop is a deliverable. Basis: AGENTS.md:43
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

`[LJ-1.523]`'s bridge, which forms with no holes, and a proof that IT needs the
ambient fact. **Nothing says the target does.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS WHERE THE STAGE LANDING COMES FROM.** Read
`[LJ-1.523]`'s bridge and say at `file:line` **which step lands a conclusion
inside `Lset (fst δ)` and why that step is there.** If it is there to satisfy
`GCHStatement`, the answer is that the landing is forced and this task stops. If
it is there to satisfy an intermediate the bridge chose, name the intermediate.

**DO NOT PROVE B5 AND DO NOT REFUTE B5.** Whether an ambient injection exists is
not settled inside this development. `[LJ-1.550]` did not try and neither should
you.

**YOU MAY TAKE THE TWO INJECTIONS AS HYPOTHESES.** They are B9 and B10 and both
are open. **This task is about whether an ambient cardinality fact stands
between those two injections and `GCHStatement`, and about nothing else.**

**IF THE ROUTE EXISTS, IT RE-PRICES THE WHOLE JOIN, SO STATE ITS HYPOTHESES IN
FULL.** A route with a hidden hypothesis is worse than no route.

**DO NOT BUILD B9, B10 OR THE ASSIGNMENT.** AD12 gives this brief one
obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## WHERE THE STAGE LANDING CAME FROM`.** The step at
`file:line`, and whether the target or the bridge put it there.

**REQUIRED REPORT SECTION `## THE HYPOTHESES OF THE ROUTE`.** Every hypothesis
of what you built, listed, with a mark against any that is ambient. **If the
list is empty of ambient facts, say so in those words.**

ESTIMATE: about 140 lines in the probe, of which the obligation is about 35.
BASIS: `[LJ-1.550]` rebuilt one implication of the bridge at a comparable size.
Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the stage landing itself.

    -- the step of [LJ-1.523]'s bridge whose conclusion sits in Lset (fst δ),
    -- restated alone, TYPE ONLY

**Write it FIRST and typecheck it ALONE.** Until it is isolated you cannot say
whether anything else needs it. ESTIMATE: about 12 lines, under 60 seconds.

## WHAT GO AND NO-GO EACH EARN

**A GO REMOVES THE ONLY INPUT THAT ASKS FOR SOMETHING OUTSIDE L**, and it means
`[LJ-1.523]`'s bridge is one route and not the route.

**A NO-GO SAYS THE STAGE LANDING IS FORCED BY THE TARGET**, and then the
mathematician must report to the owner that `L ⊨ GCH` as stated here needs an
ambient cardinality fact. That is a ruling, and it is worth knowing now.

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
  changed_files_none = ["agents/tasks/LJ-1-558/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-558/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-558/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-558/Probe558.agda"]
  changed_files_none = ["agents/tasks/LJ-1-558/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-558/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 232.057)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 196.125)
- CANDIDATE archive/dev/JOURNAL.md  (score 194.269)
- CANDIDATE dev/ARCHIVE.md  (score 154.538)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 150.342)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 71.590)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 60.969)
- CANDIDATE dev/literature/digest.md  (score 54.152)
- CANDIDATE dev/literature/geology.md  (score 47.227)
- CANDIDATE dev/literature/terms-2026-08.md  (score 41.068)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
