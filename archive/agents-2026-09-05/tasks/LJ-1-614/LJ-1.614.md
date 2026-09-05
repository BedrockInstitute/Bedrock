# LJ-1.614: restate G+ at the stage carrier, which is the mathematician's ruling

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-614/Probe614.agda`:

    graph-stage-at : <`GraphStageAt ψ₀`, face G+ RESTATED at the stage carrier
                      with the guard>

Land nothing in `src/`. **You are not asked for `[LJ-1.606]`'s original G+.**

**`[LJ-1.610]` IS A NO-GO AND IT ASKED ME FOR A RULING. THIS IS THE RULING.** Its
section `## THE JUDGEMENT THE OWNER OWES`:

> "Walls 2 to 4 are **RULINGS, not research**: the face's type as `[LJ-1.606]`
> wrote it fixes arity 3, the hull carrier, and the all-index discipline, and
> **the tree's graph machinery fits none of the three.** The cheaper repair is to
> restate G+ at the stage carrier with the guard, **as this probe already does**
> (`GraphStageAt ψ₀`); the stronger repair is an arity-4 kit with the bound as a
> slot. **Wall 1 is RESEARCH**: the sequence-in-stage construction, priced by
> nobody yet."

**I RULE THE CHEAPER REPAIR AND I SAY WHY.** The stronger repair changes the
kit's arity, which would re-open face E, and `[LJ-1.609]` just PAID face E at
the frame the crossing consumes. **A repair that unpays a delivered face is not
cheaper in any sense.**

**AND THE CHEAPER REPAIR IS ALREADY PROTOTYPED.** `GraphStageAt ψ₀` exists in
`[LJ-1.610]`'s own probe. **Import it, do not restate it**: R-42 measures a
cross-file respelling of one object at 1.74 s against 155.02 s.

**WHAT THIS COSTS THAT THE ORIGINAL DID NOT.** A restated face must still be
consumed by `[LJ-1.606]`'s `Crossing`. **Say at `file:line` whether the crossing
accepts `GraphStageAt` in place of `GraphStage`**, and if it does not, say
exactly what else must move. **That is the real risk in this task and it is why
it is not a transcription.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-614/Probe614.agda::graph-stage-at"]

## SCOPE (write)
- agents/tasks/LJ-1-614/Probe614.agda
- agents/tasks/LJ-1-614/lj-1.614-report.md
- agents/tasks/LJ-1-614/review-of-graph-stage-at.md
- agents/tasks/LJ-1-614/runs/

## PREMISES

1. `[LJ-1.610]` is a NO-GO and names the two repairs. Basis: agents/tasks/LJ-1-610/review-of-graph-stage.md:78
2. Its probe already carries `GraphStageAt ψ₀`. Basis: agents/tasks/LJ-1-610/Probe610.agda:1
3. `[LJ-1.606]` states the original face G+. Basis: agents/tasks/LJ-1-606/Probe606.agda:156
4. Its `Crossing` bundles the faces. Basis: agents/tasks/LJ-1-606/Probe606.agda:178
5. `[LJ-1.609]` is GO and paid face E. Basis: agents/tasks/LJ-1-609/lj-1.609-report.md:1
6. The kit cannot be filled with junk. Basis: agents/tasks/LJ-1-606/Probe606.agda:260
7. `[LJ-1.602]` found the shared root of row 3's failures. Basis: agents/tasks/LJ-1-602/lj-1.602-report.md:1
8. Devlin's Σ₁ form is witnessed inside the carrier. Basis: dev/literature/devlin-II5.md:222
9. `Σ₁` has an unbounded-quantifier constructor. Basis: src/FOL/LevyHierarchy.lagda.md:75
10. `defSet` reads under the world's inner satisfaction. Basis: src/L/Definability.lagda.md:111
11. R-42 rules the respelling cost. Basis: dev/LESSONS.md:4404
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

Face E paid, the crossing built, and `GraphStageAt ψ₀` prototyped in a
predecessor's probe. **The restated face is consumed by nothing.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE CONSUMER.** Read `[LJ-1.606]`'s
`Crossing` (`Probe606.agda:178-180`) and say at `file:line` **what it demands of
face G+.** Then say whether `GraphStageAt` meets that demand. **If it does not,
this task is a kit change and not a face build: say so before spending.**

**DO NOT BUILD THE ARITY-4 KIT.** That is the stronger repair and I have ruled
against it, because it would re-open face E which `[LJ-1.609]` just paid.
**If you find the cheaper repair cannot work without it, say so and stop**: that
overturns my ruling and I want it overturned by measurement, not worked around.

**DO NOT ATTEMPT WALL 1.** `[LJ-1.610]` calls the sequence-in-stage construction
RESEARCH, priced by nobody. **It is not funded here.**

**DO NOT BUILD FACE G-.** `[LJ-1.611]` is a NO-GO on it and its cure is
separately queued.

**CAP EVERY TYPECHECK ON A WALL CLOCK YOU SET AND REPORT THE CAP**, and report
peak RSS: this family has heap-walled twice.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## DOES THE CROSSING ACCEPT IT`.** At `file:line`,
with what else had to move.

**REQUIRED REPORT SECTION `## WHAT THE CROSSING NOW WANTS`.** Of the three faces,
which are paid after this task. **Do not read a discharge into anything you did
not inhabit.**

ESTIMATE: about 160 lines in the probe, of which the obligation is about 40.
BASIS: `[LJ-1.610]` prototyped the restated face. **The risk is the consumer, not
the face.** Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the crossing's demand on G+.

    -- Crossing's G+ slot, re-ascribed against GraphStageAt, TYPE ONLY, capped

**Write it FIRST, typecheck it ALONE, cap it.** If the slot rejects the restated
face, everything else in this brief is void and you will know in the first hour.
ESTIMATE: about 12 lines, cap at two minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO LEAVES THE CROSSING WANTING ONLY G-**, and row 3 would have one named
blocker instead of three.

**A NO-GO THAT SHOWS THE CROSSING REJECTS THE RESTATED FACE OVERTURNS MY
RULING**, and then the arity-4 kit is the only repair and the campaign must
price re-opening face E.

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
  changed_files_none = ["agents/tasks/LJ-1-614/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-614/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-614/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-614/Probe614.agda"]
  changed_files_none = ["agents/tasks/LJ-1-614/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-614/review-of-*.md"]

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
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 227.521)
- CANDIDATE archive/dev/JOURNAL.md  (score 216.860)
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 216.689)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 180.258)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 180.170)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 67.992)
- CANDIDATE dev/literature/digest.md  (score 54.548)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 53.598)
- CANDIDATE dev/literature/terms-2026-08.md  (score 48.192)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 37.548)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
