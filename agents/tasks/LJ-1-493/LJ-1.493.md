# LJ-1.493: repair B, at the real frame, before any landing

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-493/Probe493.agda`:

    someEnv-inlined :
        (the frame of src/L/Condensation.lagda.md:3509-3515, rebuilt)
      → (the type that `someEnv ya yc b a ar c yaK ycK arK` returns at :3515)

**by opening `SupplyEnv` at the `KValue` telescope and NOT by calling the
`someEnv` field.** This is Repair B's one remaining cost, priced at its own site.
Land nothing in `src/`.

**THE MATHEMATICIAN HAS RULED REPAIR B.** `[LJ-1.488]` priced Repair A and
Repair B and declined to choose (`agents/tasks/LJ-1-488/lj-1.488-report.md:339`).
The ruling is Repair B, on three grounds: it names 5 site groups against 7 at the
same 3 chapters (`:324`, `:302`); it deletes a field instead of growing one; and
**P-l decides it**, because Repair A adds a `gam` binder to `someEnvDef`, a type
that is today tower-generic (`:304-305`), which is a presentation in a type and
not a fact about a stage. You do not re-open that choice.

**TAKE `⟨ ω ∈ sucV gam ⟩`, NEVER `⟨ ω ∈ gam ⟩`.** `[LJ-1.491]` is GO and built
the stronger `⟨ ω ∈ gam ⟩` at `KValue`, but its own report says the landing wants
the gate `SupplyEnv` actually states (`agents/tasks/LJ-1-491/lj-1.491-report.md:244-247`),
which is `src/L/Coding/EnvSupply.lagda.md:111`. `ω ∈ gam` excludes `gam = ω`; the
`sucV` gate does not, and no landed consumer authorises that exclusion.

**READ `[LJ-1.483]` FIRST AND DO NOT REPEAT ITS FRAME.** It STOPPED because the
domain of `codesK` at ITS frame was empty
(`agents/tasks/LJ-1-483/lj-1.483-report.md:93-94`). At the real site the two
inputs `codesK` needs are already in scope from the surrounding proof
(`src/L/Condensation.lagda.md:3509`). Reproducing the real frame is the whole
risk and it is this task's W3.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-493/Probe493.agda::someEnv-inlined"]

## SCOPE (write)
- agents/tasks/LJ-1-493/Probe493.agda
- agents/tasks/LJ-1-493/lj-1.493-report.md
- agents/tasks/LJ-1-493/review-of-someEnv-inlined.md
- agents/tasks/LJ-1-493/runs/

## PREMISES

1. `[LJ-1.488]` priced Repair A and Repair B and did not choose. Basis: agents/tasks/LJ-1-488/lj-1.488-report.md:339
2. Repair B names 5 site groups; Repair A names 7. Basis: agents/tasks/LJ-1-488/lj-1.488-report.md:324
3. Repair A would put a `gam` binder on a tower-generic type. Basis: agents/tasks/LJ-1-488/lj-1.488-report.md:305
4. `[LJ-1.491]` is GO: `KValue` can carry the gate, and no landed consumer loses an instance. Basis: agents/tasks/LJ-1-491/lj-1.491-report.md:200
5. `KValue` is the only module in the chain that binds `gam`. Basis: src/L/Condensation.lagda.md:7380
6. The gate `SupplyEnv` states is `⟨ ω ∈ sucV gam ⟩`. Basis: src/L/Coding/EnvSupply.lagda.md:111
7. The call to replace is at the `:3515` binding. Basis: src/L/Condensation.lagda.md:3515
8. `arNum` is already bound one line group above it. Basis: src/L/Condensation.lagda.md:3509
9. `[LJ-1.483]` STOPPED on an empty `codesK` domain at its own probe frame. Basis: agents/tasks/LJ-1-483/lj-1.483-report.md:93
10. Its W3 nevertheless typechecked, so the shape is reachable. Basis: agents/tasks/LJ-1-483/lj-1.483-report.md:92
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**ELEVEN DISPATCHES HAVE MEASURED THIS FIELD AND NONE HAS WRITTEN ITS TERM.**
The geography is now complete: `[LJ-1.488]` says where each gate CAN be stated,
`[LJ-1.491]` says the frame CAN carry the one gate that had no home, and
`[LJ-1.483]` says which probe frame is too poor to try it in. What is left is one
term at the real frame.

## WHAT IS MISSING

The frame, and the inlined term inside it.

## THE REASONING

**D-10, BEFORE ANY AGDA.** `[LJ-1.483]`'s stop is a measurement of a PROBE
FRAME, not of the site. Say, at `file:line`, which inputs `codesK` needs, and
whether each is in scope at `src/L/Condensation.lagda.md:3509` in the landed
proof. **If the real frame cannot be reproduced in a probe at all, STOP AND SAY
SO**: that finding rules out every probe-first route and makes the landing the
only one, which is a real deliverable and not a failure.

**THE SHAPE.** Rebuild the telescope down to `PropAgree`'s frame. Give it `lam`,
`gam` and `⟨ ω ∈ sucV gam ⟩`. Open `SupplyEnv` there. Inline the `someEnv` call.
Do not import a probe, and do not import `[LJ-1.491]`'s `Probe491.agda`.

**DO NOT DELETE ANYTHING AND DO NOT EDIT `src/`.** Repair B retires
`someEnvDef`, `LFacts.someEnv` and `TFacts.someEnv`, but a retirement is a
landing and this task is not the landing. Measure the replacement; leave the
originals untouched.

**DO NOT FUND THIS AGAINST `[LJ-1.491]`'s 2.40 s.** Its own report forbids it
(`agents/tasks/LJ-1-491/lj-1.491-report.md:259-260`). That pad measured a record
telescope, not this frame.

**REQUIRED REPORT SECTION `## WHAT REPAIR B STILL OWES`.** Restate
`[LJ-1.488]`'s five site groups with the ones this task measures marked, and say
for each remaining group whether it is a deletion, a re-parameterisation, or an
unmeasured cost. **Do not claim the landing.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 150 lines in the probe, of which the obligation is
about 40. BASIS: `[LJ-1.483]` rebuilt a neighbouring frame at a comparable depth
and stopped at its application. Comparables are of SHAPE and nothing may be
funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the frame itself, because `[LJ-1.483]` is the one measurement of it and it
came back empty.

    frame-reachable : (the two inputs codesK needs, at the :3509 frame)

**Write it FIRST, with the obligation omitted, and typecheck it ALONE.** It must
put `c∈` and `shEq` in scope at the frame that `codesK` is applied in, WITHOUT
postulating either. If it will not form, the probe route is closed and the task
stops at its cheapest point with the strongest finding it could carry.

ESTIMATE for W3: about 35 lines and under 40 seconds. **Do not fund it against
`[LJ-1.483]`'s W3**: that one supplied the inputs by hand and this one may not.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO GIVES THE LANDING ITS PAD** and turns Repair B from two priced types into
one measured term with four deletions behind it.

**A NO-GO AT THE FRAME RULES OUT EVERY PROBE-FIRST ROUTE TO THIS FIELD**, which
would be the first time this campaign could say that a landing is the only way to
measure a repair, and it would change how the next nine briefs are written.

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
  changed_files_none = ["agents/tasks/LJ-1-493/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-493/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-493/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-493/Probe493.agda"]
  changed_files_none = ["agents/tasks/LJ-1-493/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-493/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 210.864)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 192.267)
- CANDIDATE archive/dev/JOURNAL.md  (score 179.135)
- CANDIDATE dev/ARCHIVE.md  (score 172.203)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 151.258)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 53.339)
- CANDIDATE dev/literature/terms-2026-08.md  (score 50.046)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 47.372)
- CANDIDATE dev/literature/digest.md  (score 45.763)
- CANDIDATE dev/literature/geology.md  (score 37.436)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
