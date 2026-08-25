# LJ-1.464: how far the shift code reaches, and what is left of Residue

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-464/Probe464.agda`:

    residue-at-successor :
        (γ : S) (oγ : IsOrd (fst γ)) (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
        (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩)
      → ⟨ fst (κC (sucʟ γ) (suc-ord oγ)) ∈ˢ fst (sucʟ γ) ⟩

**`Residue` at every successor of an infinite L-ordinal, from the code
`[LJ-1.460]` delivered.** Land nothing in `src/`.

**READ TWO REPORTS BEFORE ANY AGDA, AND STOP IF EITHER VERDICT IS NOT `GO`.**
`agents/tasks/LJ-1-460/lj-1.460-report.md` (`:108`, committed `0e4295c`) and
`agents/tasks/LJ-1-446/lj-1.446-report.md` (`:72`, committed `816702c`). Quote
both delivered types.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-464/Probe464.agda::residue-at-successor"]

## SCOPE (write)
- agents/tasks/LJ-1-464/Probe464.agda
- agents/tasks/LJ-1-464/lj-1.464-report.md
- agents/tasks/LJ-1-464/review-of-residue-at-successor.md
- agents/tasks/LJ-1-464/runs/

## PREMISES

1. `[LJ-1.460]` is GO: a code for the shift injection at a successor. Basis: agents/tasks/LJ-1-460/lj-1.460-report.md:108
2. Its delivered term is at the probe that typechecked. Basis: agents/tasks/LJ-1-460/Probe460.agda:73
3. The shift is an ambient injection from the successor into the ordinal. Basis: src/L/Absorption.lagda.md:614
4. Its graph is carved as an L-element by one separation. Basis: src/L/Absorption.lagda.md:604
5. `[LJ-1.446]` is GO: the coded least cardinal is never strictly below the ambient one. Basis: agents/tasks/LJ-1-446/lj-1.446-report.md:72
6. The coded selection is least among the coded-injection ordinals. Basis: agents/tasks/LJ-1-430/Probe430.agda:89
7. `Residue` is `[LJ-1.447]`'s one hypothesis. Basis: agents/tasks/LJ-1-447/Probe447.agda:207
8. A refutation measures the site it names and never how far that site extends. Basis: dev/LESSONS.md:3752
9. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
10. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**`[LJ-1.460]` PUT THE FIRST CODE FOR A NON-IDENTITY INJECTION IN THIS TREE**,
and nothing has spent it. It codes `sucʟ γ ↪ γ`. The coded least cardinal of
`sucʟ γ` is least among the ordinals that `sucʟ γ` coded-injects into, so that
code bounds it by `γ`, and `γ ∈ sucʟ γ`.

## WHAT IS MISSING

The application, and the honest statement of what it does NOT reach.

## THE REASONING

**D-10, BEFORE ANY AGDA.** `[LJ-1.460]` delivers `∥ Σ[ F ∈ S ] InjCode F (sucʟ γ) γ ∥₁`
and `κC`'s selection predicate is a truncated coded injection at a member of the
successor carrier (`agents/tasks/LJ-1-430/Probe430.agda:82-84`). **Write both
types out and say whether the delivered code IS an inhabitant of that predicate
at `d := γ`.** If the carrier indices differ, name the repackaging; do not hide
it in a `subst`.

**THE SHAPE.** Rebuild the coded selection as `[LJ-1.446]` does
(`Probe446.agda:117-166`), take `[LJ-1.460]`'s code as a module hypothesis at its
delivered type, feed it to the selection's minimality, and conclude membership.
Do not import a probe. Do not rebuild the carve.

**REQUIRED REPORT SECTION `## WHAT IS LEFT OF RESIDUE`, AND IT IS THE POINT OF
THIS TASK.** `Residue` quantifies over ALL infinite ordinals `y` with
`κL(y) ∈ y`. This term covers the SUCCESSORS. **State, as a type, what remains:
the LIMIT ordinals `y` with `κL(y) ∈ y`.** Say whether the shift route reaches
them and give the evidence. **Do not claim `Residue`.** One class is not the
band, and C-42 rules that in both directions.

**DO NOT POSTULATE AND DO NOT ADD A HYPOTHESIS TO CLOSE THE LIMIT CASE.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 130 lines in the probe, of which the obligation is
about 25. BASIS: `agents/tasks/LJ-1-446/Probe446.agda` is about 210 lines and
rebuilds the same selection plus one application; this file rebuilds the
selection and applies a hypothesis. Comparables are of SHAPE.

## W3, THE WIDEST UNMEASURED TERM

It is whether the delivered code fits the selection's predicate without
repackaging.

    fits : ⟨ CodedInjP' d ⟩

**Write it FIRST at `d` the index of `γ` in the successor carrier, from
`[LJ-1.460]`'s code as a module hypothesis, and typecheck it ALONE with the
obligation omitted.** `[LJ-1.460]` codes into `γ` as an L-element; the selection
ranges over `⟪ sucV (fst a) ⟫` and lifts with `upα`. **If the two do not meet,
that mismatch IS the finding**: it would say the tree's one delivered code does
not plug into the tree's one coded selection.

ESTIMATE for W3: about 12 lines and under 10 seconds.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO CUTS `Residue` DOWN TO THE LIMIT ORDINALS**, and it does it with a code
this tree now owns rather than with a hypothesis.

**A NO-GO SAYS THE ONE DELIVERED CODE DOES NOT PLUG INTO THE ONE CODED
SELECTION**, which is a defect between two green results and must be found.

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
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-464/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-464-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-464/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-464/Probe464.agda"]
  changed_files_none = ["agents/tasks/LJ-1-464/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-464/review-of-*.md"]

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
