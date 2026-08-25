# LJ-1.470: land the code without moving a single existing line

## HEAD
head_slot: coder
machine: exclusive

## THE OBLIGATION

Land ONE term in a NEW master `src/L/CodedShift.lagda.md`:

    shift-coded :
        (γ : S) (oγ : IsOrd (fst γ)) (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
        (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩)
      → ∥ Σ[ F ∈ S ] InjCode F (sucʟ γ) γ ∥₁

and register it in `src/Everything.lagda.md` after `import L.Absorption` (`:376`)
and before `import L.SquareLawClosed` (`:387`).

**A NEW MASTER, AND THE REASON IS MEASURED.** `[LJ-1.469]` landed this term
INSIDE `src/L/Absorption.lagda.md` and it was GREEN: exit 0, median 5.34 s, ratio
0.0055 against a bar of 0.0123, obligation discharged. **It still parked.**
Acceptance conjunct 4 compares the unbound-hypothesis findings as `file:line`
strings against a pre-flight snapshot (`scripts/pod/accept.py:195-207`), and
widening an import at `:37` shifted two existing findings in that same file from
`:398`/`:400` to `:399`/`:401`. **Two unchanged findings read as new, the
conjunct failed and the run exited 1.**

**SO DO NOT EDIT `src/L/Absorption.lagda.md` AT ALL.** Import from it. A new
master moves no existing line and cannot trip that comparison.

**READ ONE REPORT BEFORE ANYTHING ELSE.** `agents/tasks/LJ-1-460/lj-1.460-report.md`,
verdict `GO` at `:108`, committed `0e4295c`, term at `Probe460.agda:73-88`.

## OBLIGATION NAMES
obligations = ["src/L/CodedShift.lagda.md::shift-coded"]

## SCOPE (write)
- src/L/CodedShift.lagda.md
- dev/ledger.toml
- agents/tasks/LJ-1-470/lj-1.470-report.md
- agents/tasks/LJ-1-470/review-of-shift-coded.md
- agents/tasks/LJ-1-470/runs/
- `src/Everything.lagda.md` (R18, program-generated: wire the new master here, because acceptance conjunct 3 refuses a catalog that does not import it)

## PREMISES

1. `[LJ-1.460]` is GO on `shift-coded`, the first code for a non-identity injection in this tree. Basis: agents/tasks/LJ-1-460/lj-1.460-report.md:108
2. Its body takes all four `InjCode` conjuncts from `ShiftGraph`'s own exports and adds no hypothesis. Basis: agents/tasks/LJ-1-460/Probe460.agda:81
3. `ShiftGraph` opens its carve publicly. Basis: src/L/Absorption.lagda.md:604
4. Acceptance conjunct 4 is a SET DIFFERENCE over `file:line` findings. Basis: scripts/pod/accept.py:206
5. Two findings live in `L.Absorption` today and a line shift moves both. Basis: src/L/Absorption.lagda.md:398
6. `InjCode` is four conjuncts. Basis: src/L/Cardinal.lagda.md:223
7. The catalog imports `L.Absorption` before the slot this master takes. Basis: src/Everything.lagda.md:376
8. `[LJ-1.464]` already spends this code and is GO. Basis: agents/tasks/LJ-1-464/lj-1.464-report.md:89
9. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
10. A new top-level directory carries a README; a new MASTER inside an existing directory does not. Basis: AGENTS.md:59
11. `make check` is the gate before any commit. Basis: AGENTS.md:75
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

The term, twice: as `[LJ-1.460]`'s probe and as `[LJ-1.469]`'s green but parked
edit. **Neither is in the tree.** Two later tasks have rebuilt it from a probe
because no master offers it.

## WHAT IS MISSING

A master that does not disturb its neighbour's line numbers.

## THE REASONING

**D-10, BEFORE ANY AGDA.** Quote `[LJ-1.460]`'s term and `ShiftGraph`'s four
exported conjuncts. **Say in one line that the new master needs only imports
from `src/`.** If it needs anything from a probe, stop.

**THE SHAPE.** Create the master. Import `L.Absorption` for `ShiftGraph`,
`L.Cardinal` for `InjCode`, and whatever `[LJ-1.460]` imports for the rest. Copy
the term. Register it in the catalog. Update `dev/ledger.toml`. **Change no line
of any existing master except the one catalog import.**

**IF `src/Everything.lagda.md` IS ITSELF A MASTER WITH FINDINGS BELOW YOUR
INSERT POINT, SAY SO AND REPORT WHAT CONJUNCT 4 DID.** The checker reads tracked
masters; a catalog line inserted at `:377` shifts every import below it.
**Measure it, do not assume it.** Run `scripts/measure/check-unbound-hyp.py
--check` BEFORE and AFTER your edit, and put both outputs in the report.

**DO NOT WIDEN THE STATEMENT.** One code, one shape, under the numeral
hypothesis. Do not claim `amb-to-coded`.

**THIS TASK RUNS `machine: exclusive`.** Run ONE Agda process.

**THE RATIO BAR IS LIVE.** `[LJ-1.469]` measured 5.34 s over 543 in-fence lines
inside `L.Absorption`. A new master has a much smaller divisor, so **expect the
rate to be far higher and possibly over the bar.** Report the two numbers, the
quotient and the record's `concurrency` in `## THE RATIO`. **Do not pad the
master to move the number.**

**PROSE IS FROZEN** (`AGENTS.md:69`). **NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 45 in-fence lines. BASIS: `[LJ-1.460]`'s term is 16
lines including its `where` block and a new master carries a module header and
an import block; `src/L/StageBound.lagda.md` was 79 in-fence lines at its first
landing. Comparables are of SHAPE.

## W3, THE WIDEST UNMEASURED TERM

It is conjunct 4 again, at the catalog.

    before-and-after : the finding set of check-unbound-hyp.py

**Run the checker BEFORE any edit and keep the output. Then create the master,
register it, and run the checker again.** If the catalog insert shifts a finding
in a tracked master, the same trap fires at a new site and this task must say so
rather than discover it at acceptance.

ESTIMATE for W3: two runs, under 30 seconds each. **The comparison is the
measurement and this brief does not predict it.**

Run `make check` before and after.

## WHAT GO AND NO-GO EACH EARN

**A GO PUTS THE FIRST NON-IDENTITY CODE IN A CHAPTER** and stops later briefs
rebuilding it from a probe.

**A NO-GO SAYS THE CATALOG INSERT TRIPS THE SAME COMPARISON**, which would mean
no landing anywhere can avoid it and the gate needs the maintainer, not another
brief.

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
# No delta key: measured on LJ-1.453. The exclusion: measured on LJ-1.459.
id = "ratio-bar"
priority = 11
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 0
  heap_wall = false
  seconds_per_line_min = 0.0123
  changed_files_none = ["agents/tasks/LJ-1-470/review-of-LJ-*-*.md"]

[[branch]]
# THE ACCEPTANCE ITSELF CAN FAIL, AND NOTHING IN THIS TEMPLATE USED TO MATCH IT.
# MEASURED 2026-08-21 on LJ-1.469: the term was GREEN and its ratio was 0.0055,
# well under the bar, but acceptance conjunct 4 FAILED and the run exited 1.
# Every branch keyed on exit 0 or 42 missed, so the task parked `no-match` with a
# delivered obligation. An acceptance failure is a real event and it routes to a
# critic rather than to silence.
id = "accept-failed"
priority = 14
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 1
  changed_files_none = ["agents/tasks/LJ-1-470/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-470/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-470-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-470/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["src/L/CodedShift.lagda.md"]
  changed_files_none = ["agents/tasks/LJ-1-470/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-470/review-of-*.md"]

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
