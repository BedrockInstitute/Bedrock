# LJ-1.452: the square law as DATA over the band, under one hypothesis

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-452/Probe452.agda`, at a GENERIC band:

    sq-data-closed :
        (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
      → sq δ

under the module parameters `{ℓ} (lem) (α₀) (oα₀)`, ONE module hypothesis
`descent-both` at `[LJ-1.447]`'s DELIVERED type, and its `residue` parameter.
**There is no truncation in the conclusion, and that is the whole point.** Land
nothing in `src/`.

**THIS OBLIGATION HAS RUN ONCE AND IT STOPPED FOR A REASON THAT IS NOT
MATHEMATICS.** `[LJ-1.448]` held it. `[LJ-1.447]` was still RUNNING when the
program dispatched it, so the report it was ordered to read did not exist, and
it stopped correctly. **THAT REPORT IS IN THE TREE NOW**, committed at
`ef44a34`: `agents/tasks/LJ-1-447/lj-1.447-report.md`, verdict `GO` at `:53`,
term at `agents/tasks/LJ-1-447/Probe447.agda:207-257`.

**READ IT BEFORE ANYTHING ELSE.** If it does not exist, or its verdict is not
`GO`, write nothing and stop. **Take the hypothesis type from the probe that
typechecked and never from `[LJ-1.447]`'s brief** (`dev/pod/audit-2026-08-20.md:34`).

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-452/Probe452.agda::sq-data-closed"]

## SCOPE (write)
- agents/tasks/LJ-1-452/Probe452.agda
- agents/tasks/LJ-1-452/lj-1.452-report.md
- agents/tasks/LJ-1-452/review-of-sq-data-closed.md
- agents/tasks/LJ-1-452/runs/

## PREMISES

1. `[LJ-1.447]` is GO on `descent-both`, the four-case split at both least cardinals, with a DATA conclusion. Basis: agents/tasks/LJ-1-447/lj-1.447-report.md:53
2. Its delivered term is generic in `x` and carries `residue` as one module hypothesis. Basis: agents/tasks/LJ-1-447/Probe447.agda:207
3. `[LJ-1.437]` is GO on the same band statement with the conclusion TRUNCATED, and its recursion is the one this task reuses. Basis: agents/tasks/LJ-1-437/lj-1.437-report.md:17
4. That recursion has three branches and only the third splits on a cardinal. Basis: agents/tasks/LJ-1-437/Probe437.agda:305
5. The finite branch is closed by the motive's own hypothesis, and the `ω` branch by the chapter's `squareω`. Basis: agents/tasks/LJ-1-437/Probe437.agda:307
6. The band membership yields the ordinal certificate the motive wants. Basis: agents/tasks/LJ-1-437/Probe437.agda:284
7. The consumer of this family wants DATA, and it is landed in `src/`. Basis: src/L/StageBound.lagda.md:33
8. `[LJ-1.434]` is GO on that consumer under a TRUNCATED family, and the gap is stated there and not inhabited. Basis: agents/tasks/LJ-1-434/Probe434.agda:56
9. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
10. The architecture is a CANDIDATE and only a measurement settles it. Basis: dev/pod/screen.toml:10
11. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THE RECURSION IS WRITTEN AND GREEN, AND SO IS ITS THIRD BRANCH.**
`agents/tasks/LJ-1-437/Probe437.agda:298-348` runs the `∈`-induction at the
motive `Goal x = IsOrd x → infinite x → ∥ sq x ∥₁`. Two of its three branches
carry no truncation of their own. `[LJ-1.447]` now delivers the third as DATA.

## WHAT IS MISSING

The same recursion at the UNTRUNCATED motive. Nobody has run it.

## THE REASONING

**D-10, BEFORE ANY AGDA.** Write the two motives side by side:

    Goal437 x = IsOrd x → (⟨ x ∈ ω ⟩ → Empty.⊥) → ∥ sq x ∥₁
    Goal452 x = IsOrd x → (⟨ x ∈ ω ⟩ → Empty.⊥) → sq x

Say in one line which branches of `Probe437.agda:305-310` change and which do
not. If more than the third branch changes, the plan is wrong and the report
says so.

**THE SHAPE.**

1. Copy the imports, `band-ord` (`Probe437.agda:284-288`) and the `ord-tri`
   split (`:305-310`). Do not import a probe.
2. Take `descent-both` as a MODULE HYPOTHESIS at `[LJ-1.447]`'s delivered type,
   with `residue` carried at the module level. **Do not rebuild either seal and
   do not restate the four cases.** This file holds no `κL` and no `κC`.
3. Do W3 first, then the obligation.

**THE INDUCTION HYPOTHESIS CHANGES SHAPE AND YOU MUST WATCH IT.**
`descent-both` takes its induction hypothesis in the order
`(y) → ⟨ y ∈ˢ x ⟩ → IsOrd y → infinite y → sq y`, while `∈-induction` supplies
`(y) → ⟨ y ∈ x ⟩ → Goal y` and `Goal` takes the certificate first
(`Probe437.agda:298`). **Adapt at the call site with a lambda and report the
adapter.** If the two cannot be adapted without a `subst`, that is a finding.

**REQUIRED REPORT SECTION `## DOES IT MEET THE CONSUMER`.** State, as types and
at `file:line`, `sq-data-closed` and the landed `SqFam`
(`src/L/StageBound.lagda.md:33-38`). One quantifies `(δ : V ℓ)` and reads
membership as `∈`; the other quantifies `(δ : S)` and reads it as `∈ˢ`. **Write
the adapter as a plain function, typecheck it, and report whether it is the
identity.** If it is, the counting leg's consumer is fed under one hypothesis
and you say exactly that. If it is not, name the repackaging and do NOT hide it
inside a `subst`.

**DO NOT CLAIM THE TROPHY AND DO NOT CLAIM THE CAMPAIGN CLOSES.** The
conclusion holds under `residue`, which nothing in this tree proves.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 120 lines in the probe, of which the obligation
and its recursion are about 30. BASIS: `Probe437.agda` spends 66 lines on the
recursion INCLUDING the cardinal split this file does not carry, and
`agents/tasks/LJ-1-420/Probe420.agda` is 99 lines for an assembly of this class.
Comparables are of SHAPE, and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the `ω` branch, because it is the one place where the truncation was NOT
put there by the arrow.

    omega-branch : (x : V ℓ) → x ≡ ω → sq x
    omega-branch x x≡ω = subst sq (sym x≡ω) squareω

**Write it FIRST, with the obligation omitted, and typecheck it ALONE.**
`squareω` comes from `L.InjChain` (`Probe437.agda:51`) and `Probe437.agda:308`
uses it under `∣_∣₁`. **If `squareω` is itself truncated, this branch cannot be
untruncated and the whole task stops there.**

ESTIMATE for W3: two lines and under 3 seconds. BASIS: `Probe437.agda:308` is
the same line with one `∣_∣₁` around it.

Report the median wall time and the peak RSS over three forced rechecks at the
pane's caliber, for W3 alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO PUTS THE COUNTING LEG'S SUPPLY HALF IN DATA FORM UNDER ONE NAMED
HYPOTHESIS**, and with the landed consumer it says the bounded-subset lemma's
conclusion follows from `residue` alone.

**A NO-GO IS WORTH AS MUCH.** It says the truncation in `[LJ-1.437]` was not
only the arrow's, and `[LJ-2.5]` must be told that.

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
  changed_files_any = ["agents/tasks/LJ-1-452/review-of-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-452/Probe452.agda"]
  changed_files_none = ["agents/tasks/LJ-1-452/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-452/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 199.789)
- CANDIDATE archive/dev/JOURNAL.md  (score 194.861)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 185.059)
- CANDIDATE archive/dev/DD-archived.md  (score 159.797)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 156.133)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 58.311)
- CANDIDATE dev/literature/devlin-II5.md  (score 56.775)
- CANDIDATE dev/literature/digest.md  (score 45.104)
- CANDIDATE dev/literature/terms-2026-08.md  (score 32.002)
- CANDIDATE dev/literature/geology.md  (score 30.987)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
