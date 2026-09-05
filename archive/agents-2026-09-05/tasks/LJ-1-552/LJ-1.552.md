# LJ-1.552: the assignment at the heart of GCH

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-552/Probe552.agda`:

    succ-assignment :
        (δ κ : S) → SuccCardL δ κ
      → ∥ Σ[ s ∈ (⟪ fst δ ⟫ → S) ]
             ( ((k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
             × ((k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k') ) ∥₁

the FIRST THREE components of `[LJ-1.549]`'s `Residue`
(`agents/tasks/LJ-1-549/Probe549.agda:668-677`): an assignment from the members
of δ to L-sets, every value a subset of κ, and injective. **You do NOT build
`Link`.** Land nothing in `src/`.

**THIS IS THE MATHEMATICAL CONTENT OF B10 AND I SAY SO PLAINLY.** `[LJ-1.549]`
is a NO-GO, upheld by its critic, and it measured the obstruction exactly:
`approx-carve`'s method reaches the table, and **two of its inputs do not
exist**, the ambient assignment `s` and its object-language description `Link`
(`agents/tasks/LJ-1-549/review-of-succ-into-subsets.md`, FINDING 2). This brief
takes the first. **`residue-pays-B10` (`Probe549.agda:685-689`) spends the whole
residue for B10 outright**, so these three components plus `Link` are the row.

**WHAT `[LJ-1.549]` ALSO KILLED, SO YOU DO NOT REPEAT IT.** `[LJ-1.546]`'s
reduction of B10 to `SuccIntoSubsets` **buys nothing**: `powL κ ≡ 𝒫 κ`
(`Probe549.agda:133-136`), so the two are the same problem, proved in both
directions (`:179-181`, `:186-190`). **Do not look for a smaller `b`.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-552/Probe552.agda::succ-assignment"]

## SCOPE (write)
- agents/tasks/LJ-1-552/Probe552.agda
- agents/tasks/LJ-1-552/lj-1.552-report.md
- agents/tasks/LJ-1-552/review-of-succ-assignment.md
- agents/tasks/LJ-1-552/runs/

## PREMISES

1. `Residue` is stated in full by `[LJ-1.549]`. Basis: agents/tasks/LJ-1-549/Probe549.agda:668
2. It suffices for B10 outright. Basis: agents/tasks/LJ-1-549/Probe549.agda:685
3. `[LJ-1.549]` is a NO-GO and names the two missing inputs. Basis: agents/tasks/LJ-1-549/review-of-succ-into-subsets.md:63
4. Its critic upheld the stop. Basis: agents/tasks/LJ-1-549/review-of-LJ-1-549-1.md:1
5. `powL κ ≡ 𝒫 κ`, so the `b` freedom is worth nothing. Basis: agents/tasks/LJ-1-549/Probe549.agda:133
6. `SuccCardL`'s fourth component is a leastness clause. Basis: src/L/GCH.lagda.md:47
7. `[LJ-1.515]` built `swo-rank′`. Basis: agents/tasks/LJ-1-515/lj-1.515-report.md:1
8. `[LJ-1.531]` proved the rank injective. Basis: agents/tasks/LJ-1-531/lj-1.531-report.md:1
9. `[LJ-1.528]` built `CardAboveL` under `--safe` with no choice. Basis: agents/tasks/LJ-1-528/Probe528.agda:638
10. A stop is a deliverable. Basis: AGENTS.md:43
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

Seven of `[LJ-1.523]`'s ten inputs, and a residue that names what B10 needs.
**The assignment itself is delivered nowhere.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS WHERE THE ASSIGNMENT COMES FROM.** Say at
`file:line` what you take `s k` to BE. **Say it before you build.** The classical
argument is that every member of δ has L-cardinality at most κ, so it can be
coded by a subset of κ once a well-order is chosen; **name the term in this tree
that chooses it**, or say there is none.

**THE INJECTIVITY IS THE HALF THAT USUALLY FAILS, NOT THE SUBSET CLAUSE.** Two
different members of δ must get two different subsets. **Say which term gives
you that**, and do not assume a coding is injective because it looks canonical:
`[LJ-1.531]` had to prove the rank injective as its own obligation.

**THE CONCLUSION IS TRUNCATED, SO A CHOICE INSIDE THE TRUNCATION IS ALLOWED IF
THE TREE ALREADY HAS IT.** `[LJ-1.528]` built its predecessor under `--safe`
with no choice, and matching that is worth trying, **but do not spend the
estimate defending a purity you were not asked for. Report which you used.**

**IF THE LEASTNESS CLAUSE IS WHAT YOU NEED, SAY SO AT THE STEP.**
`SuccCardL`'s fourth component (`src/L/GCH.lagda.md:51-52`) quantifies over
every ordinal L-cardinal above κ. This bridge has failed at a universally
quantified cardinal hypothesis before.

**DO NOT BUILD `Link`. DO NOT BUILD B9 OR B5.** AD12 gives this brief one
obligation, and `Link` is a separate task already queued as `[LJ-1.554]`.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## WHAT s IS`.** Name the assignment, say what term
chose the well-order, and say whether the construction is choice-free.

**REQUIRED REPORT SECTION `## WHAT LINK WOULD HAVE TO SAY`.** Three sentences.
Given the `s` you built, **say what a `Formula S 3` describing it must express**,
and whether anything in `src/FOL/` states that shape today. Do not build it.
**That is what `[LJ-1.554]` needs.**

ESTIMATE: about 200 lines in the probe, of which the obligation is about 50.
BASIS: `[LJ-1.531]`'s injectivity proof is the nearest comparable. **This is an
uncertain estimate: the assignment is the classical content of the theorem and
nobody in this campaign has built one.** Comparables are of SHAPE and nothing
may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the well-order that picks a coding for each member of δ.

    -- the term in this tree that gives, for a member of δ, a bijection to a
    -- subset of κ, or the sentence that there is none

**Write it FIRST and typecheck it ALONE.** If the tree has no such term, say so
and stop: that is the measurement, and it costs one hour instead of five.
ESTIMATE: about 25 lines, under 2 minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS THREE OF THE RESIDUE'S FOUR COMPONENTS**, and with `Link` it pays
B10 outright by a term that already exists.

**A NO-GO THAT NAMES THE MISSING WELL-ORDER IS THE MOST VALUABLE STOP THIS
CAMPAIGN COULD PRODUCE**, because it would say the GCH leg needs a construction
the tree has never had, and how big it is.

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
  changed_files_none = ["agents/tasks/LJ-1-552/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-552/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-552/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-552/Probe552.agda"]
  changed_files_none = ["agents/tasks/LJ-1-552/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-552/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 163.872)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 158.213)
- CANDIDATE archive/dev/JOURNAL.md  (score 155.643)
- CANDIDATE dev/ARCHIVE.md  (score 130.209)
- CANDIDATE archive/dev/DD-archived.md  (score 117.715)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 52.371)
- CANDIDATE dev/literature/digest.md  (score 46.638)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 44.883)
- CANDIDATE dev/literature/terms-2026-08.md  (score 31.486)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 28.921)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
