# LJ-1.469: land the code, in the chapter that already carved it

## HEAD
head_slot: coder
machine: exclusive

## THE OBLIGATION

Land ONE term in `src/L/Absorption.lagda.md`, after `ShiftGraph`:

    shift-coded :
        (γ : S) (oγ : IsOrd (fst γ)) (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
        (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩)
      → ∥ Σ[ F ∈ S ] InjCode F (sucʟ γ) γ ∥₁

**THE HOME IS FORCED AND IT IS NOT A NEW MASTER.** `L.Absorption` already holds
`ShiftGraph` (`:538`) and already imports `L.Cardinal` (`:37`, `using ( _↪_ )`).
**Widen that import to carry `InjCode` and nothing else.** No new chapter, no new
catalog entry, no new README.

**READ ONE REPORT BEFORE ANYTHING ELSE.** `agents/tasks/LJ-1-460/lj-1.460-report.md`,
verdict `GO` at `:108`, committed `0e4295c`. Its term is at
`agents/tasks/LJ-1-460/Probe460.agda:73-88` and its body is
`∣ SG.G , code ∣₁` with the four conjuncts taken straight from `ShiftGraph`'s own
exports. If that report does not exist or its verdict is not `GO`, write nothing
and stop.

## OBLIGATION NAMES
obligations = ["src/L/Absorption.lagda.md::shift-coded"]

## SCOPE (write)
- src/L/Absorption.lagda.md
- dev/ledger.toml
- agents/tasks/LJ-1-469/lj-1.469-report.md
- agents/tasks/LJ-1-469/review-of-shift-coded.md
- agents/tasks/LJ-1-469/runs/

## PREMISES

1. `[LJ-1.460]` is GO on `shift-coded`, the first code for a non-identity injection in this tree. Basis: agents/tasks/LJ-1-460/lj-1.460-report.md:108
2. Its delivered term is at the probe that typechecked. Basis: agents/tasks/LJ-1-460/Probe460.agda:73
3. Its four conjuncts come from `ShiftGraph`'s own exports and it adds no hypothesis. Basis: agents/tasks/LJ-1-460/Probe460.agda:81
4. `ShiftGraph` is in this chapter and opens its carve publicly. Basis: src/L/Absorption.lagda.md:604
5. The chapter already imports `L.Cardinal`. Basis: src/L/Absorption.lagda.md:37
6. `InjCode` is four conjuncts. Basis: src/L/Cardinal.lagda.md:223
7. `[LJ-1.464]` already spends this code and is GO. Basis: agents/tasks/LJ-1-464/lj-1.464-report.md:89
8. `[LJ-1.465]` is spending it again at the other selection, and is live. Basis: agents/tasks/LJ-1-465/LJ-1.465.md:9
9. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
10. `make check` is the gate before any commit. Basis: AGENTS.md:75
11. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69
12. One SRC collection after LJ-1. Basis: dev/pod/direction.md:37

## WHAT IS DELIVERED ALREADY

**THIS CAMPAIGN'S MOST REUSABLE RESULT IS SITTING IN A PROBE.** `amb-to-coded` is
NO-GO three times, every one at the graph of a `leastOf` selection. `[LJ-1.460]`
coded a DEFINABLE function instead and it went through in one dispatch, on a
carve this chapter had already run. **Two tasks have spent it already**
(`[LJ-1.464]` GO, `[LJ-1.465]` live) and both had to rebuild it from a probe,
because no master offers it.

## WHAT IS MISSING

The chapter-level term. A probe is not a library.

## THE REASONING

**D-10, BEFORE ANY AGDA.** Quote `[LJ-1.460]`'s term in full and quote
`ShiftGraph`'s four exported conjuncts at `file:line`. **Say in one line that the
term needs nothing this chapter does not already have.** If it does, name what,
and stop.

**THE SHAPE.** Widen the `L.Cardinal` import at `:37` to carry `InjCode`. Put
the term after `ShiftGraph` closes. Do not move `ShiftGraph`, do not touch
`Carve`, and do not import a probe. Update `dev/ledger.toml`.

**DO NOT WIDEN THE STATEMENT.** It is one code at one shape, `sucʟ γ ↪ γ`, under
the numeral hypothesis. **Do not state it at a general pair and do not claim
`amb-to-coded`.**

**REQUIRED REPORT SECTION `## WHAT THIS UNBLOCKS`.** Name, at `file:line`, the
tasks that rebuilt this term from a probe, and say that a chapter-level term
removes that rebuild. **Do not claim it settles `Residue`**: `[LJ-1.464]` covers
successors that hold every numeral, and the limit case is open.

**THIS TASK RUNS `machine: exclusive`.** Every seconds key is guarded by
`concurrency == 1` (`scripts/pod/table.py:575`). **Run ONE Agda process.**

**THE RATIO BAR IS LIVE AND THE DIVISOR IS THE WHOLE CHAPTER.** `L.Absorption`
is a large master, so the rate may well fall under the bar even though the
addition is small. **Report the in-fence line count, the median wall, the
quotient and the record's `concurrency` in a section `## THE RATIO`.** Do not
pad and do not trim the chapter to move the number.

**PROSE IS FROZEN** (`AGENTS.md:69`). **NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 20 in-fence lines added. BASIS:
`[LJ-1.460]`'s whole term is 16 lines including its `where` block
(`Probe460.agda:73-88`) and the import widening is one token. Comparables are of
SHAPE.

## W3, THE WIDEST UNMEASURED TERM

It is the chapter's own check time, because the divisor is the whole master and
nobody has measured `L.Absorption` under this caliber.

    baseline : the chapter as it stands today

**Typecheck `src/L/Absorption.lagda.md` UNCHANGED first, three forced rechecks,
and report the median.** Then add the term and measure again. **The difference
is what this landing costs and the quotient is what the bar reads.** A chapter
this size has never been measured here, and a brief that guessed the number
would be funding against a comparable.

ESTIMATE for W3: unknown, and the brief refuses to guess it. `L.Absorption` is
526 in-fence lines by the ledger's caliber; at the parameterized band of law P-m
that would be a few seconds, and at the instantiation band it would be far more.
**The measurement decides which, and that is the point of running it alone.**

Run `make check` before and after.

## WHAT GO AND NO-GO EACH EARN

**A GO PUTS THE FIRST NON-IDENTITY CODE IN A CHAPTER**, so later briefs cite a
master instead of rebuilding a probe.

**A NO-GO SAYS THE TERM NEEDS SOMETHING THE CHAPTER LACKS**, which would mean
`[LJ-1.460]`'s probe carried a supplier no master offers, and that is worth
finding.

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
  seconds_per_line_max = 0.0123

[[branch]]
# BOTH EXCLUSIONS DELIBERATE. No delta key: measured on LJ-1.453, a closing
# record carried delta 0 and a row keyed on -1 missed. The changed_files_none:
# measured on LJ-1.459, the coder_adversarial critic returns the same master at
# the same line count and the row re-escalated itself
# (dev/pod/transitions/2026-08.jsonl:1241-1242).
id = "ratio-bar"
priority = 11
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 0
  heap_wall = false
  seconds_per_line_min = 0.0123
  changed_files_none = ["agents/tasks/LJ-1-469/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-469/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-469-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-469/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["src/L/Absorption.lagda.md"]
  changed_files_none = ["agents/tasks/LJ-1-469/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-469/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 218.591)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 203.028)
- CANDIDATE archive/dev/JOURNAL.md  (score 163.680)
- CANDIDATE dev/ARCHIVE.md  (score 142.303)
- CANDIDATE archive/dev/DD-archived.md  (score 140.452)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 57.645)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 53.054)
- CANDIDATE dev/literature/terms-2026-08.md  (score 49.180)
- CANDIDATE dev/literature/digest.md  (score 42.507)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 34.326)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
