# LJ-1.465: the second remainder its own author named

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-465/Probe465.agda`:

    residue-at-successor-446 :
        (γ : S) (oγ : IsOrd (fst γ)) (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
        (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩)
      → ⟨ fst (κC (sucʟ γ) (suc-ord oγ)) ∈ˢ fst (sucʟ γ) ⟩

where `κC` is **`[LJ-1.446]`'s coded selection** and not the one
`[LJ-1.464]` used. Land nothing in `src/`.

**`[LJ-1.464]` NAMED THIS REMAINDER ITSELF AND REFUSED TO CLAIM IT.** Its GO
covers the coded selection at the shift code's own stage, not `[LJ-1.446]`'s
(`agents/tasks/LJ-1-464/lj-1.464-report.md`, section `## WHAT IS LEFT OF
RESIDUE`). **That refusal is correct and this task is the difference.**

**READ TWO REPORTS BEFORE ANY AGDA, AND STOP IF EITHER VERDICT IS NOT `GO`.**
`agents/tasks/LJ-1-464/lj-1.464-report.md` (`:89`, committed `7fe14b3`) and
`agents/tasks/LJ-1-446/lj-1.446-report.md` (`:72`, committed `816702c`).

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-465/Probe465.agda::residue-at-successor-446"]

## SCOPE (write)
- agents/tasks/LJ-1-465/Probe465.agda
- agents/tasks/LJ-1-465/lj-1.465-report.md
- agents/tasks/LJ-1-465/review-of-residue-at-successor-446.md
- agents/tasks/LJ-1-465/runs/

## PREMISES

1. `[LJ-1.464]` is GO at a coded selection that is NOT `[LJ-1.446]`'s, and its report says so. Basis: agents/tasks/LJ-1-464/lj-1.464-report.md:89
2. Its delivered term takes the code as an explicit argument. Basis: agents/tasks/LJ-1-464/Probe464.agda:199
3. Its `κC` is local to that probe. Basis: agents/tasks/LJ-1-464/Probe464.agda:166
4. `[LJ-1.446]`'s `κC` is the one the campaign's other results use. Basis: agents/tasks/LJ-1-446/Probe446.agda:194
5. `[LJ-1.446]` is GO on the ordering between the two least cardinals. Basis: agents/tasks/LJ-1-446/lj-1.446-report.md:72
6. `[LJ-1.460]` is GO on the code the two selections would share. Basis: agents/tasks/LJ-1-460/lj-1.460-report.md:108
7. `Residue` is landed as a type and names `κL` and `κC` as parameters. Basis: src/L/StageBound.lagda.md:51
8. A refutation, and a GO, measure the site they name and never how far it extends. Basis: dev/LESSONS.md:3752
9. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
10. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

`[LJ-1.460]` codes `sucʟ γ ↪ γ`. `[LJ-1.464]` spends that code against a coded
selection built at the code's own stage and gets membership. `[LJ-1.446]` builds
the selection the rest of the campaign uses, over `⟪ sucV (fst a) ⟫` with `upα`.
**Nobody has shown the same code reaches the second selection.**

## WHAT IS MISSING

One bound-crossing. The code lives at its own stage; `[LJ-1.446]`'s predicate
ranges over a different carrier.

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE WHOLE TASK.** Write the two selection
predicates side by side at `file:line`: `[LJ-1.464]`'s (`Probe464.agda:160-170`)
and `[LJ-1.446]`'s (`Probe446.agda:158-166`). **Say exactly which index, carrier
or bound differs.** If they differ in more than the bound, name every difference
before writing a term.

**THE SHAPE.** Rebuild `[LJ-1.446]`'s selection as that probe carries it. Take
`[LJ-1.460]`'s code as a module hypothesis at its delivered type. Show the code
inhabits `[LJ-1.446]`'s predicate at the right index, then apply minimality. Do
not import a probe. Do not rebuild the carve.

**DO NOT WIDEN THE CLAIM.** This is successors that hold every numeral. It is
not `Residue`, and the limit case is untouched. **Say so in one line.**

**DO NOT POSTULATE AND DO NOT ADD A HYPOTHESIS TO CROSS THE BOUND.**

**REQUIRED REPORT SECTION `## WHAT RESIDUE STILL OWES`.** After this term, state
as a type what remains of `Residue`: the LIMIT ordinals, at
`[LJ-1.464]`'s `Residue-at-limit` shape. **Do not attempt it and do not price
it from this task's seconds.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 170 lines in the probe, of which the obligation is
about 30. BASIS: `agents/tasks/LJ-1-446/Probe446.agda` is about 210 lines and
rebuilds this selection plus one application. Comparables are of SHAPE.

## W3, THE WIDEST UNMEASURED TERM

It is the bound crossing, and it is the cheapest place this task can die.

    fits-446 : ⟨ CodedInjP' d ⟩

**Write it FIRST at `d` the index of `γ` in `[LJ-1.446]`'s carrier, from the code
as a module hypothesis, and typecheck it ALONE with the obligation omitted.**
`[LJ-1.460]` codes into `γ` as an L-element; `[LJ-1.446]` lifts with `upα` over
`⟪ sucV (fst a) ⟫`. **If the two do not meet, that mismatch is the finding**: it
says this tree's one delivered code does not reach the selection the campaign's
other results are stated at.

ESTIMATE for W3: about 12 lines and under 10 seconds.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO PUTS `Residue`'s SUCCESSOR CASE AT THE SELECTION THE CAMPAIGN ACTUALLY
USES**, so the landed `Residue` (`src/L/StageBound.lagda.md:51`) is reduced to
limits and nothing else.

**A NO-GO SAYS THE ONE DELIVERED CODE DOES NOT REACH THAT SELECTION**, which is a
gap between two green results and must be found now, not later.

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
  changed_files_any = ["agents/tasks/LJ-1-465/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-465-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-465/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-465/Probe465.agda"]
  changed_files_none = ["agents/tasks/LJ-1-465/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-465/review-of-*.md"]

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
