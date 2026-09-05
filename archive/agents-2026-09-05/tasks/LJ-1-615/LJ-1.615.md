# LJ-1.615: ValueIsL, the tractable half of a factorization that was proved once

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-615/Probe615.agda`:

    value-is-L : <`ValueIsL`, the second factor of `[LJ-1.611]`'s recovered
                  `ambientOnly-from`>

Land nothing in `src/`. **You are NOT asked for `TransferL` and NOT asked for
`AmbientOnly`.**

**`[LJ-1.611]` IS A NO-GO AND IT RECOVERED A PROVED FACTORIZATION FROM THE
RETIRED ROUTE.** Its section `## THE MEASURED PRECEDENT, CUT AND RECOVERABLE`:

> "**THE AMBIENT FORM WAS BUILT ONCE, ON THE RETIRED ROUTE, AND ONLY REDUCED.**
> At commit `3f5001e` the then-`src/L/Condensation.lagda.md` stated `AmbientOnly`
> ... and **PROVED the factorization `ambientOnly-from : TransferL → ValueIsL →
> AmbientOnly`**: the ambient form follows from an ambient-to-inner transfer of
> the graph formula at `L` plus the value's constructibility. **Neither factor
> was delivered there.**"

**SO THE IMPLICATION IS PROVED AND BOTH FACTORS ARE OPEN. I FUND ONE, AND I SAY
WHICH AND WHY.**

**`ValueIsL` IS THE VALUE'S CONSTRUCTIBILITY. `TransferL` IS AN AMBIENT-TO-INNER
TRANSFER.** `[LJ-1.611]` measured, in the same report, that G-'s proof meets the
direction `[LJ-1.533]` named: **"Code buys ambient. Ambient buys nothing."**
`TransferL` runs in exactly that unpaid direction. **`ValueIsL` does not, and
that is the whole reason this brief takes it.**

**AND ROW 3 DID NOT MERGE WITH THE OTHER LINE.** `[LJ-1.611]` was explicit:
G- "IS NOT THE `[LJ-1.533]` SHAPE... `GraphAmbient`'s type is satisfiable (the
junk terms prove it) and its conclusion is an ambient path equation, not a code,
so no such type-level obstruction exists here." **Row 3 remains an independent
line and this task works on it.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-615/Probe615.agda::value-is-L"]

## SCOPE (write)
- agents/tasks/LJ-1-615/Probe615.agda
- agents/tasks/LJ-1-615/lj-1.615-report.md
- agents/tasks/LJ-1-615/review-of-value-is-L.md
- agents/tasks/LJ-1-615/runs/

## PREMISES

1. `[LJ-1.611]` is a NO-GO and recovers the factorization. Basis: agents/tasks/LJ-1-611/lj-1.611-report.md:79
2. It states G- is not the `[LJ-1.533]` shape. Basis: agents/tasks/LJ-1-611/lj-1.611-report.md:1
3. `[LJ-1.533]` measured "Code buys ambient. Ambient buys nothing." Basis: agents/tasks/LJ-1-533/lj-1.533-report.md:76
4. Its type-level refutation is at its own report. Basis: agents/tasks/LJ-1-533/lj-1.533-report.md:40
5. `[LJ-1.606]` states face G-. Basis: agents/tasks/LJ-1-606/Probe606.agda:168
6. The kit cannot be filled with junk. Basis: agents/tasks/LJ-1-606/Probe606.agda:260
7. `[LJ-1.609]` is GO and paid face E. Basis: agents/tasks/LJ-1-609/lj-1.609-report.md:1
8. `LsetGraphAt` is the graph formula. Basis: src/L/Condensation.lagda.md:1
9. `isL` is the constructibility predicate. Basis: src/L/Constructible.lagda.md:379
10. `[LJ-1.607]` found a recorded cure with no surviving code. Basis: archive/dev/LJ-dispatch-index.md:212
11. R-42 rules the respelling cost. Basis: dev/LESSONS.md:4404
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

A proved factorization on a retired route, with neither factor delivered, and a
measurement that one of the two runs in the direction that does not pay.

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE RECOVERY.** `[LJ-1.611]` names commit
`3f5001e` and the then-`src/L/Condensation.lagda.md`. **Recover the statement of
`ValueIsL` from `[LJ-1.611]`'s report, which quotes it, and say at `file:line`
what it asks.** **Do not go digging in git history for the old file**: the report
is the delivered evidence and `[LJ-1.607]` measured what happens when a campaign
chases a name whose code is gone.

**STATE IT AT TODAY'S CARRIER, NOT THE RETIRED ONE.** The route it came from is
retired. **Say at `file:line` what changes when you move it.**

**IF `ValueIsL` TURNS OUT TO NEED `TransferL`, SAY SO AND STOP.** That would mean
the factorization does not split the way its author thought, and it would put
row 3 back into the unpaid direction. **That is a full result and I want it in
the hour it lands.**

**DO NOT BUILD `TransferL` OR `AmbientOnly`.** AD12 gives this brief one
obligation, and `TransferL` runs in the direction `[LJ-1.533]` measured as
unpaid.

**CAP EVERY TYPECHECK ON A WALL CLOCK YOU SET AND REPORT THE CAP**, and report
peak RSS.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE STATEMENT AT TODAY'S CARRIER`.** In full, with
what changed from the retired form.

**REQUIRED REPORT SECTION `## DOES IT NEED TransferL`.** Two sentences, yes or
no, with the site. **This decides whether row 3 stays an independent line.**

ESTIMATE: about 170 lines in the probe, of which the obligation is about 45.
**Uncertain: the statement is recovered from a report quoting a retired file,
and nobody has stated it at today's carrier.** Comparables are of SHAPE and
nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is `ValueIsL` at today's carrier.

    -- ValueIsL, restated at today's carrier, TYPE ONLY, capped

**Write it FIRST, typecheck it ALONE, cap it.** If it will not state here, the
recovery does not transfer and you say so at once. ESTIMATE: about 12 lines, cap
at two minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS ONE OF TWO FACTORS OF A PROVED IMPLICATION**, and leaves face G-
wanting only the factor that runs the hard way.

**A NO-GO SAYING `ValueIsL` NEEDS `TransferL` COLLAPSES THE FACTORIZATION**, and
row 3 would then meet the same one-way street as the other line, which is a
ruling and not a funding question.

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
  changed_files_none = ["agents/tasks/LJ-1-615/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-615/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-615/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-615/Probe615.agda"]
  changed_files_none = ["agents/tasks/LJ-1-615/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-615/review-of-*.md"]

[[branch]]
# PARK, NOT ESCALATE. MEASURED on LJ-1.534, 2026-08-22: this row matched
# a heap wall FOUR times, exit 251 each, to attempt_max. A critic
# re-runs the same probe and re-hits the same wall, so an escalation can only
# loop. **A heap wall is a resource fact and no critic can adjudicate it.**
id = "heap-wall-park"
priority = 30
action = "park"

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
  Full entry: dev/LESSONS.md:2307
- **P-l. A statement may be ABOUT a concrete stage without dragging that stage's PRESENTATION into its type**
  **The law.** Being about a concrete position is not what costs. Naming a transparent construction in a statement's TYPE is. If the tower's stage values are `opaque` upstream, a theorem may quantify over, hypothesize about and conclude at `Sset ω` freely, because the stage is an ATOM to the elaborator and nothing unfolds. If instead the type mentions a transparent presentation, such as `⟪ sucV (...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2367
- **D-26. A well-founded key on a tower needs generation data, or it needs syntax**
  **Rule:** When a route must well-order a cumulative tower's stage, ask first what the stage's members CARRY. A stage built as the values of finitely many total operations carries its own generation data, so a well-founded key exists with NO syntax at all: the operation index, then the arguments, ordered recursively. A stage built as a definable power carries nothing: its members are sets, not c...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:1735
- **C-42. A refutation measures the site it names, and it never measures how far that site extends**
  **Rule:** A refutation is a measurement of ONE site. It says the statement there is false. **It says nothing about how many other sites carry the same false shape.** So when a refutation lands, the next action is not the cure. **It is the sweep: search the tree for the shape, and report the COUNT before you price the cure.** A cure funded against the named site is priced against a number nobody...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:3762

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev, archive/scripts, dev/ARCHIVE.md:
- CANDIDATE dev/ARCHIVE.md  (score 182.891)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 170.105)
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 163.665)
- CANDIDATE archive/dev/JOURNAL.md  (score 154.767)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 146.862)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 70.729)
- CANDIDATE dev/literature/digest.md  (score 50.142)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 47.188)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 41.288)
- CANDIDATE dev/literature/geology.md  (score 40.089)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
