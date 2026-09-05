# LJ-1.572: Def for B9's g, from the code the leg already assembled

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-572/Probe572.agda`:

    b9-g-is-definable : <`[LJ-1.568]`'s `Def a b g` at B9's own `g`>

where B9's `g` is the map `⟪ Lset δ ⟫ → ⟪ δ ⟫` that `[LJ-1.561]`'s `w→B9`
hands in (`agents/tasks/LJ-1-561/Probe561.agda:376-381`). Land nothing in
`src/`.

**`[LJ-1.568]` IS GO AND IT MADE THE WALL EXACT.** It found the weakest
restriction on `W` and then proved it is **NECESSARY as well as sufficient**:
`def-restricted` (`agents/tasks/LJ-1-568/Probe568.agda:252-253`) inhabits
`Restrict Def`, and `graph→def` (`:368-371`) turns the conclusion back into
`Def`. **So `W` at a given `g` is EQUIVALENT to `g` being definable**, and
there is nothing weaker to look for.

**`Def a b g` IS: SOME `Formula S 3` DESCRIBES `g` ON THE MEMBERS OF `a`, IN
BOTH DIRECTIONS** (`Probe568.agda:189-190`, from `[LJ-1.554]`'s `LinkAt`).
**It asks for no Levy grade, no stage, no size bound and no choice principle**,
because the carve runs through `hasSeparationL`, which takes an ARBITRARY
formula (`src/L/Axioms/Full.lagda.md:144`).

**AND B9's `g` IS THE ONE MAP THIS CAMPAIGN HAS ALREADY WRITTEN FORMULAS FOR.**
`[LJ-1.566]` is GO: `InjCode` is ASSEMBLED, all four conjuncts in one term,
after `[LJ-1.524]`, `[LJ-1.529]`, `[LJ-1.531]` and `[LJ-1.559]` built them
separately. `svAt`, `domAt` and `injAt` ARE formulas about the rank
(`src/L/Cardinal.lagda.md:225-227`). **If any `g` in this development is
definable, it is this one.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-572/Probe572.agda::b9-g-is-definable"]

## SCOPE (write)
- agents/tasks/LJ-1-572/Probe572.agda
- agents/tasks/LJ-1-572/lj-1.572-report.md
- agents/tasks/LJ-1-572/review-of-b9-g-definable.md
- agents/tasks/LJ-1-572/runs/

## PREMISES

1. `[LJ-1.568]` is GO and states `Def`. Basis: agents/tasks/LJ-1-568/Probe568.agda:189
2. It proves `Def` sufficient. Basis: agents/tasks/LJ-1-568/Probe568.agda:252
3. It proves `Def` necessary. Basis: agents/tasks/LJ-1-568/Probe568.agda:368
4. It records that no grade, stage, bound or choice is needed. Basis: agents/tasks/LJ-1-568/lj-1.568-report.md:1
5. `hasSeparationL` takes an arbitrary formula. Basis: src/L/Axioms/Full.lagda.md:144
6. `[LJ-1.561]` pays B9 from `W`. Basis: agents/tasks/LJ-1-561/Probe561.agda:376
7. `[LJ-1.566]` is GO and assembled `InjCode`. Basis: agents/tasks/LJ-1-566/lj-1.566-report.md:1
8. `InjCode`'s three formula conjuncts are `svAt`, `domAt`, `injAt`. Basis: src/L/Cardinal.lagda.md:225
9. `[LJ-1.559]` built `domAt`. Basis: agents/tasks/LJ-1-559/lj-1.559-report.md:1
10. `[LJ-1.564]`'s bill has B9 as row 4. Basis: agents/tasks/LJ-1-564/Probe564.agda:456
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

An assembled `InjCode`, an exact characterisation of what `W` needs, and a
proof that nothing weaker will do. **No term says B9's `g` is definable.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE ARITY.** `Def` wants a `Formula S 3`
(`Probe568.agda:189`). `InjCode`'s conjuncts are formulas at their own arities
(`src/L/Cardinal.lagda.md:225-227`). **Say at `file:line` what arity each is and
whether they can be brought to 3.** If they cannot, say so before you spend the
estimate: that is the whole risk in this task.

**`Def` WANTS BOTH DIRECTIONS AND `InjCode` MAY ONLY GIVE ONE.** Read
`Probe568.agda:189-190` and say which of the two readings the assembled code
already supplies and which you must build. **Say it before you build either.**

**DO NOT REBUILD ANY CONJUNCT.** `[LJ-1.566]` assembled them. Import its term.

**IF `[LJ-1.566]`'s FRAME IS NOT B9's FRAME, SAY SO AND STOP.** `[LJ-1.548]`
stopped for a comparable reason and it cost one hour instead of five. A named
frame mismatch is a full result.

**DO NOT ATTEMPT ROWS 1, 2, 3 OR 5.** AD12 gives this brief one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## THE FORMULA AND ITS ARITY`.** What you used, at
`file:line`, its arity, and what you had to change.

**REQUIRED REPORT SECTION `## WHAT THIS DOES TO THE BILL`.** `[LJ-1.564]`'s bill
is five rows. **Say exactly which rows this task pays and which it does not, and
do not read a discharge into anything you did not inhabit.** `[LJ-1.571]` set
that standard this hour and it is the right one.

ESTIMATE: about 170 lines in the probe, of which the obligation is about 40.
BASIS: `[LJ-1.568]` built `Def` and its two directions at a comparable size.
Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is B9's `g` itself, written out.

    -- the g at [LJ-1.561]'s w→B9 call site, its definition unfolded, TYPE ONLY

**Write it FIRST and typecheck it ALONE.** You cannot say a map is definable
before you have looked at the map. ESTIMATE: about 12 lines, under 60 seconds.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS ROW 4 OF FIVE**, and `[LJ-1.561]` showed the same `W` pays B7 and
`Link` too.

**A NO-GO THAT NAMES THE ARITY OR THE MISSING DIRECTION IS A FULL RESULT**,
because it would say the coding leg's formulas do not answer the question they
were built for, and the mathematician must know that before funding more of
them.

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
  changed_files_none = ["agents/tasks/LJ-1-572/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-572/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-572/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-572/Probe572.agda"]
  changed_files_none = ["agents/tasks/LJ-1-572/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-572/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 179.618)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 164.211)
- CANDIDATE archive/dev/JOURNAL.md  (score 142.911)
- CANDIDATE dev/ARCHIVE.md  (score 135.120)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 114.080)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 53.972)
- CANDIDATE dev/literature/devlin-II5.md  (score 52.782)
- CANDIDATE dev/literature/digest.md  (score 44.250)
- CANDIDATE dev/literature/terms-2026-08.md  (score 38.122)
- CANDIDATE dev/literature/geology.md  (score 35.620)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
