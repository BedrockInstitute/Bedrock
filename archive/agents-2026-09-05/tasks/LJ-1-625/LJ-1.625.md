# LJ-1.625: the landing survey, finished, with the one cell LJ-1.620 filled

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-625/Probe625.agda`:

    landing-survey : <for each of the four PAID `class-pred` ingredients, the
                      chapter of `src/` that could host it, stated as a term
                      naming the module and the import edge it would add, or
                      the term naming what blocks it>

Land nothing in `src/`. **This SURVEYS a landing, it does not perform one.**

**`[LJ-1.620]` CARRIED THIS OBLIGATION AND DID NOT DELIVER IT.** Its probe is
RED: `witness.py` reports `exit 42 inside the probe: Syntax.WrongContentBlock`,
`1 UNRESOLVED of 1`, `probe_red=True`. **That is a literate-Agda content-block
error, not mathematics.** Its report is a skeleton whose cells still read
`(FILLED)`. The row parked at `attempt_max:sys-lint-accept`.

**ONE CELL WAS REAL, AND I CHECKED IT MYSELF BEFORE PUTTING IT IN THIS BRIEF:**

> ingredient (i)'s natural home, the definability chapter `L.Definability`, **is
> blocked**: the rows need `Lset` and `𝒟ₒ` from `L.Constructible`, and
> `L.Constructible` already imports `L.Definability`
> (`src/L/Constructible.lagda.md:37`); **the reverse edge is a cycle.**

I verified both halves: `:37` reads `open import L.Definability {ℓ} using ( module DefOf )`,
and `L.Definability` does not import `L.Constructible` back. **Take that row as
given and do not re-derive it.**

**TWO SURVEYS HAVE NOW FOUND THE SAME SHAPE, AND THAT IS THE THING TO TEST.**
`[LJ-1.555]` found no existing master could host `CardAboveL` without a new
import edge. `[LJ-1.620]` found ingredient (i)'s natural home is a cycle.
**The likely general answer is that these terms sit ABOVE the chapters that
would want them, and the honest output of this survey may be "each needs a new
master".** That is a real answer, not a failure. **But measure it; do not assume
it because I said it.**

**WHY THIS MATTERS MORE THAN ITS SIZE.** Of 128 briefs I wrote this campaign, 94
said "Land nothing in `src/`" and 4 named a `src/` path. **Four `class-pred`
ingredients are paid and all four sit in probes, and nobody has asked where any
of them would live.** This is that question.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-625/Probe625.agda::landing-survey"]

## SCOPE (write)
- agents/tasks/LJ-1-625/Probe625.agda
- agents/tasks/LJ-1-625/lj-1.625-report.md
- agents/tasks/LJ-1-625/review-of-landing-survey.md
- agents/tasks/LJ-1-625/runs/

## PREMISES

1. `[LJ-1.620]`'s probe is red at parse. Basis: agents/tasks/LJ-1-620/Probe620.agda:1
2. Its report is a skeleton with unfilled cells. Basis: agents/tasks/LJ-1-620/lj-1.620-report.md:36
3. Its one real cell names the cycle. Basis: agents/tasks/LJ-1-620/lj-1.620-report.md:36
4. `L.Constructible` imports `L.Definability`. Basis: src/L/Constructible.lagda.md:37
5. `[LJ-1.555]` read the import graph over 102 masters. Basis: agents/tasks/LJ-1-555/review-of-CardAboveL-landing.md:56
6. It found no existing master could host that term. Basis: agents/tasks/LJ-1-555/review-of-CardAboveL-landing.md:81
7. `[LJ-1.613]` paid ingredients (i) and (ii). Basis: agents/tasks/LJ-1-613/Probe613.agda:137
8. `[LJ-1.600]` paid (v). Basis: agents/tasks/LJ-1-600/lj-1.600-report.md:1
9. `[LJ-1.601]` and `[LJ-1.608]` paid (iv). Basis: agents/tasks/LJ-1-608/lj-1.608-report.md:1
10. `src/Everything.lagda.md` is the aggregator. Basis: src/Everything.lagda.md:389
11. `[LJ-1.622]` measured a warm floor for a landing. Basis: agents/tasks/LJ-1-622/lj-1.622-report.md:1
12. The program commits by explicit path from the task's scope. Basis: AGENTS.md:78
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

Four paid ingredients, all in probes; one import-graph reading for a different
term; and one verified cycle for ingredient (i).

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE PARSE.** `[LJ-1.620]` died at
`Syntax.WrongContentBlock`. **Write the smallest well-formed literate-Agda probe
that binds `landing-survey` with a hole, typecheck it, and only then add
content.** A probe that does not parse cannot report anything, and that is how a
whole dispatch was lost.

**FILL EVERY CELL OR SAY WHY IT CANNOT BE FILLED.** `[LJ-1.620]` left `(FILLED)`
placeholders in a delivered report. **A placeholder in a returned report is
worse than an absent section**, because it reads as content. If you run short,
**fill fewer rows completely rather than all rows partially.**

**DO NOT RE-DERIVE INGREDIENT (i)'s CYCLE.** It is verified and quoted above.
**Start at (ii).**

**READ THE `import` LINES OF THE MASTERS UNDER `src/` AND REPORT THE COUNT YOU
READ.** **Never conclude a count from a command containing `head`.**

**A "NEEDS A NEW MASTER" ANSWER IS A REAL ANSWER.** `[LJ-1.555]` reached exactly
that. **Name the chapter it would be and what it would import.**

**DO NOT LAND ANYTHING AND DO NOT RUN `make check`.** `[LJ-1.624]` is performing
a landing under a measured recipe and this brief must not step into it.

**CAP EVERY TYPECHECK ON A WALL-CLOCK CAP YOU SET AND REPORT IT**, and report
peak RSS.

**DO NOT POSTULATE. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## FOUR INGREDIENTS, FOUR HOMES`.** One row each:
chapter, import edge added, or the blocker. **No placeholders.**

**REQUIRED REPORT SECTION `## THE CHEAPEST ONE`.** Name it, say why, and say
what a brief landing it must carry. **That sentence is what the next landing
brief will be written from**, and the last four landing briefs were written from
my guesses.

ESTIMATE: about 120 lines in the probe, of which the obligation is about 30, and
most of the work is reading rather than proving. BASIS: `[LJ-1.555]` did the
same reading for one term. Comparables are of SHAPE and nothing may be funded
against them.

## W3, THE WIDEST UNMEASURED TERM

It is a probe that parses.

    -- landing-survey with a hole, in a well-formed literate block, TYPE ONLY

**Write it FIRST and typecheck it ALONE before any content.** `[LJ-1.620]` never
got past this. ESTIMATE: about 10 lines, cap at one minute.

## WHAT GO AND NO-GO EACH EARN

**A GO GIVES THE CAMPAIGN ITS FIRST LANDING TARGET CHOSEN BY MEASUREMENT**,
for terms that are already proved and currently reachable by nothing.

**A NO-GO SAYING ALL FOUR NEED NEW MASTERS IS EQUALLY USEFUL**, because it would
price the landing as four chapters and the mathematician could say that to the
owner instead of promising it a term at a time.

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
  changed_files_none = ["agents/tasks/LJ-1-625/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-625/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-625/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-625/Probe625.agda"]
  changed_files_none = ["agents/tasks/LJ-1-625/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-625/review-of-*.md"]

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
- CANDIDATE archive/dev/JOURNAL.md  (score 250.767)
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 232.480)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 232.230)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 223.387)
- CANDIDATE dev/ARCHIVE.md  (score 199.392)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 75.238)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 57.702)
- CANDIDATE dev/literature/digest.md  (score 55.743)
- CANDIDATE dev/literature/geology.md  (score 42.829)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 38.904)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
