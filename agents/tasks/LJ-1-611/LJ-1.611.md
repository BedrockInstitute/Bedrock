# LJ-1.611: face G-, where an ambient witness pins the tower's level

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-611/Probe611.agda`:

    graph-ambient : <`GraphAmbient`, face G- of `[LJ-1.606]`'s `Crossing`>
      (`agents/tasks/LJ-1-606/Probe606.agda:168-172`)

Land nothing in `src/`.

**`[LJ-1.606]` IS GO AND NAMED THREE FACES. THIS IS THE THIRD.**

> **G- `GraphAmbient`**: any ambient witness of the carried matrix at an ORDINAL
> index pins the tower's level. **UNBUILT.** Devlin (a); **`[LJ-1.160]`'s
> `crossOut` made concrete** (`agents/tasks/LJ-1-160/ProbeLJ1160A.agda:71-72`).

**THE PRECEDENT EXISTS ON DISK AND I CHECKED.** `agents/tasks/LJ-1-160/ProbeLJ1160A.agda`
is present in this tree. **Read `crossOut` at `:71-72` before you build
anything**: `[LJ-1.606]` says G- is that term made concrete, and a term that
already exists is cheaper than one that does not.

**G- IS THE FACE THAT MAKES THE KIT NON-VACUOUS, WHICH IS UNUSUAL AND USEFUL.**
`[LJ-1.606]` proved the kit cannot be filled with junk **both ways**
(`Probe606.agda:260-285`), and the direction that bites is G-: **a TRUE matrix
fails G- outright** (`⊤-fails-G-`, `:262`), because at the ordinal `∅` it would
force every level. **So G- has real content and you cannot cheat it.**

**IT GOES THE OPPOSITE WAY FROM G+.** G+ asks the stage's inner world to satisfy
something; G- takes an AMBIENT witness and pins an internal level. **That is the
inner-to-ambient crossing in its own direction**, and it is the direction this
campaign has failed at repeatedly on other rows. **Say plainly whether that
matters here.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-611/Probe611.agda::graph-ambient"]

## SCOPE (write)
- agents/tasks/LJ-1-611/Probe611.agda
- agents/tasks/LJ-1-611/lj-1.611-report.md
- agents/tasks/LJ-1-611/review-of-graph-ambient.md
- agents/tasks/LJ-1-611/runs/

## PREMISES

1. `[LJ-1.606]` is GO and names three faces. Basis: agents/tasks/LJ-1-606/lj-1.606-report.md:119
2. Face G- is stated at its probe. Basis: agents/tasks/LJ-1-606/Probe606.agda:168
3. `crossOut` is the named precedent and it is on disk. Basis: agents/tasks/LJ-1-160/ProbeLJ1160A.agda:71
4. A TRUE matrix fails G- outright. Basis: agents/tasks/LJ-1-606/Probe606.agda:262
5. The kit cannot be filled with junk both ways. Basis: agents/tasks/LJ-1-606/Probe606.agda:260
6. `[LJ-1.602]` found the shared root of row 3's failures. Basis: agents/tasks/LJ-1-602/lj-1.602-report.md:1
7. `[LJ-1.533]` refuted a code for an arbitrary ambient injection. Basis: agents/tasks/LJ-1-533/lj-1.533-report.md:1
8. `[LJ-1.568]` proved coding is describing, necessary and sufficient. Basis: agents/tasks/LJ-1-568/Probe568.agda:377
9. `defSet` reads under the world's inner satisfaction. Basis: src/L/Definability.lagda.md:111
10. `𝒟ₒ-intro` is the one route into a stage. Basis: src/L/Constructible.lagda.md:301
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. A stop is a deliverable. Basis: AGENTS.md:43
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

A built crossing, a non-vacuity proof that turns on this very face, and
`crossOut` on disk. **Face G- is unbuilt.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS `crossOut`.** Read
`agents/tasks/LJ-1-160/ProbeLJ1160A.agda:71-72` and say at `file:line` **what it
proves and what "made concrete" would have to add.** If it instantiates almost
directly, say so and finish early: **`[LJ-1.560]`'s obligation turned out to be
an instantiation and its estimate was far too high, and that was a good
outcome.**

**AN AMBIENT WITNESS PINNING AN INTERNAL LEVEL IS THE DIRECTION THAT HAS FAILED
ELSEWHERE.** `[LJ-1.533]` refuted a code for an arbitrary ambient injection, and
four later tasks met the same wall. **Say at `file:line` whether G- is that
shape or a different one.** If it is that shape, **stop and say so**: it would
mean row 3 meets the campaign's other blocker and the two lines are one.

**DO NOT WEAKEN G- TO MAKE IT GO THROUGH.** `[LJ-1.606]` proved a TRUE matrix
fails it. **A weakened G- that a TRUE matrix satisfies is refuted before you
write it.**

**DO NOT BUILD FACES E OR G+.** AD12 gives this brief one obligation.

**CAP EVERY TYPECHECK ON A WALL CLOCK YOU SET AND REPORT THE CAP**, and report
peak RSS.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## WHAT crossOut ALREADY GIVES`.** At `file:line`,
with what you had to add.

**REQUIRED REPORT SECTION `## IS G- THE AMBIENT WALL`.** Three sentences. **Say
whether this face is the same shape `[LJ-1.533]` refuted.** That answer decides
whether row 3 is an independent line or joins the other one, and the
mathematician cannot tell from outside.

ESTIMATE: about 190 lines in the probe, of which the obligation is about 45.
BASIS: `crossOut` exists and the task is to make it concrete. **Uncertain: "made
concrete" is `[LJ-1.606]`'s phrase and not a measurement.** Comparables are of
SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is `crossOut` re-ascribed at G-'s frame.

    -- crossOut, re-ascribed at Probe606.agda:168-172's frame, TYPE ONLY, capped

**Write it FIRST, typecheck it ALONE, cap it.** ESTIMATE: about 12 lines, cap at
two minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS THE FACE THAT CARRIES THE KIT'S NON-VACUITY**, and with E and G+
would complete the crossing.

**A NO-GO SAYING G- IS THE AMBIENT WALL JOINS ROW 3 TO THE CAMPAIGN'S OTHER
BLOCKER**, which would mean one problem and not two, and the mathematician
carries that to the owner.

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
  changed_files_none = ["agents/tasks/LJ-1-611/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-611/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-611/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-611/Probe611.agda"]
  changed_files_none = ["agents/tasks/LJ-1-611/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-611/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 196.428)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 173.556)
- CANDIDATE archive/dev/JOURNAL.md  (score 169.030)
- CANDIDATE dev/ARCHIVE.md  (score 149.205)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 144.357)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 69.852)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 62.768)
- CANDIDATE dev/literature/digest.md  (score 44.461)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 41.213)
- CANDIDATE dev/literature/geology.md  (score 36.843)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
