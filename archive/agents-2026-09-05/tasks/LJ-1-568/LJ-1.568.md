# LJ-1.568: the weakest g under which W still pays three sites

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-568/Probe568.agda`:

    W-restricted : <`[LJ-1.561]`'s `W`, with the WEAKEST extra hypothesis on `g`
                    you can find, together with proofs that the restricted form
                    still gives `w→B9`, `w→B7` and `w→link`>

**Choosing the hypothesis is the deliverable.** Land nothing in `src/`.

**`[LJ-1.561]` IS GO AND IT FOUND THAT THREE OF FIVE WALLS ARE ONE.** Its `W`
(`agents/tasks/LJ-1-561/Probe561.agda:160-163`) is:

    W = (a b : S) (g : ⟪ fst a ⟫ → ⟪ fst b ⟫)
      → ((k k' : ⟪ fst a ⟫) → g k ≡ g k' → k ≡ k')
      → ∥ Σ[ G ∈ S ] IsGraph a b g G ∥₁

and it pays **B9** (`Probe561.agda:376-381`), **B7** (`:388-391`, which is the
same term), **`Link`** (`:345-353`) and **`[LJ-1.549]`'s whole `Residue`**
(`:357-362`). It does NOT pay the assignment or `StageHigh`, and it says why.

**AND IT SHARPENED WHAT IS MISSING TO ONE WORD.** Quoting its own note at
`Probe561.agda:165-168`: `[LJ-1.554]` measured that **"the graph is ALREADY an
ambient set with no hypothesis, and that what is missing is `isL` of this
set."**

**SO `W` SAYS: THE GRAPH OF AN INJECTIVE AMBIENT FUNCTION BETWEEN L-SETS IS
ITSELF AN L-SET. I DO NOT BELIEVE THAT FOR AN ARBITRARY `g` AND I SAY SO.**
`[LJ-1.533]` refuted a code for an arbitrary ambient injection. **The three
sites do not need an arbitrary `g`: each supplies a particular one.** This task
finds what they actually need.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-568/Probe568.agda::W-restricted"]

## SCOPE (write)
- agents/tasks/LJ-1-568/Probe568.agda
- agents/tasks/LJ-1-568/lj-1.568-report.md
- agents/tasks/LJ-1-568/review-of-W-restricted.md
- agents/tasks/LJ-1-568/runs/

## PREMISES

1. `[LJ-1.561]` is GO and states `W`. Basis: agents/tasks/LJ-1-561/Probe561.agda:160
2. It pays B9 from `W`. Basis: agents/tasks/LJ-1-561/Probe561.agda:376
3. It pays B7 by the same term. Basis: agents/tasks/LJ-1-561/Probe561.agda:388
4. It pays `Link` and the whole `Residue`. Basis: agents/tasks/LJ-1-561/Probe561.agda:357
5. It records that what is missing is `isL` of the graph. Basis: agents/tasks/LJ-1-561/Probe561.agda:165
6. `[LJ-1.554]` measured the graph is already an ambient set. Basis: agents/tasks/LJ-1-554/Probe554.agda:150
7. `[LJ-1.533]` refuted a code for an arbitrary ambient injection. Basis: agents/tasks/LJ-1-533/lj-1.533-report.md:1
8. The two generators of an L-set both take a `Formula`. Basis: src/L/Axioms/Full.lagda.md:144
9. `hasReplacementL` takes a `Formula S 2`. Basis: src/L/Axioms/Full.lagda.md:277
10. `[LJ-1.560]` is GO and its reflection step was an instantiation. Basis: agents/tasks/LJ-1-560/lj-1.560-report.md:1
11. `[LJ-1.526]` named a fact and `[LJ-1.528]` then built it. Basis: agents/tasks/LJ-1-526/lj-1.526-report.md:1
12. A stop is a deliverable. Basis: AGENTS.md:43
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

`W`, and four implications out of it, all typechecked. **Nothing says `W` is
true, and I do not think it is as stated.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE REFUTATION.** Try to refute `W` as
`[LJ-1.561]` states it. **If you refute it, say so at `file:line` and then the
rest of the task is the restriction.** If you cannot refute it in the D-10's
budget, say that too and move on: you are not asked to settle it.

**THE RESTRICTION MUST BE SUPPLIED BY THE THREE SITES, NOT BY YOU.** Read
`w→B9`, `w→B7` and `w→link` and see what `g` each hands in. **A hypothesis those
three cannot supply is worth nothing however weak it looks.** Say for each site,
at `file:line`, that it supplies your hypothesis.

**`[LJ-1.560]`'S REFLECTION STEP IS GO AND IT WAS AN INSTANTIATION.** Its
obligation is at `agents/tasks/LJ-1-560/Probe560.agda:165-176`. **Say whether it
supplies your hypothesis for any of the three sites.** That is the most likely
source and nobody has tried it.

**DO NOT ATTEMPT THE ASSIGNMENT OR `StageHigh`.** `[LJ-1.561]` proved `W` does
not reach either. AD12 gives this brief one obligation.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## W AS STATED`.** Refuted, or not refuted in budget.
Say which, with the term or the reason.

**REQUIRED REPORT SECTION `## THE RESTRICTION`.** The hypothesis in full, one
row per site saying whether that site supplies it, each at `file:line`.

ESTIMATE: about 190 lines in the probe, of which the obligation is about 50.
BASIS: `[LJ-1.561]` built five implications at a comparable size. Comparables
are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the `g` that `w→B9` actually hands in.

    -- the g at [LJ-1.561]'s w→B9 call site, its type written out, TYPE ONLY

**Write it FIRST and typecheck it ALONE.** The restriction has to be true of
that `g` and there is no point inventing one before you have looked at it.
ESTIMATE: about 12 lines, under 60 seconds.

## WHAT GO AND NO-GO EACH EARN

**A GO NAMES THE ONE FACT THAT CLEARS THREE OF THE CAMPAIGN'S FIVE WALLS**, and
the `[LJ-1.526]` to `[LJ-1.528]` pattern says the next task can then build it.

**A NO-GO THAT REFUTES `W` AND SHOWS NO RESTRICTION IS SUPPLIABLE IS A RULING**,
and the mathematician will carry it to the owner.

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
  changed_files_none = ["agents/tasks/LJ-1-568/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-568/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-568/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-568/Probe568.agda"]
  changed_files_none = ["agents/tasks/LJ-1-568/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-568/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 170.063)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 146.460)
- CANDIDATE archive/dev/JOURNAL.md  (score 143.773)
- CANDIDATE dev/ARCHIVE.md  (score 116.198)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 115.100)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 59.850)
- CANDIDATE dev/literature/devlin-II5.md  (score 49.147)
- CANDIDATE dev/literature/digest.md  (score 40.195)
- CANDIDATE dev/literature/terms-2026-08.md  (score 30.367)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 23.662)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
