# LJ-1.448: the square law as DATA over the whole band, under one hypothesis

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-448/Probe448.agda`, at a GENERIC band:

    sq-data-closed :
        (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
      → sq δ

under the module parameters `{ℓ} (lem) (α₀) (oα₀)`, ONE module hypothesis
`descent-both` at `[LJ-1.447]`'s DELIVERED type, and its `residue` parameter.
**There is no truncation in the conclusion, and that is the whole point.**
Land nothing in `src/`.

**READ ONE REPORT BEFORE ANYTHING ELSE:**
`agents/tasks/LJ-1-447/lj-1.447-report.md`. If it does not exist, or its
verdict is not `GO`, write nothing and stop. Say in your report which of the
two tests failed. **Take the hypothesis type from the probe that typechecked
and never from `[LJ-1.447]`'s brief.** A landing built on a brief's type is the
defect the independent audit measured twice (`dev/pod/audit-2026-08-20.md:34`).

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-448/Probe448.agda::sq-data-closed"]

## SCOPE (write)
- agents/tasks/LJ-1-448/Probe448.agda
- agents/tasks/LJ-1-448/lj-1.448-report.md
- agents/tasks/LJ-1-448/review-of-sq-data-closed.md
- agents/tasks/LJ-1-448/runs/

## PREMISES

1. `[LJ-1.437]` is GO on the same statement with the conclusion TRUNCATED, and its recursion is the one this task reuses. Basis: agents/tasks/LJ-1-437/lj-1.437-report.md:17
2. That recursion has three branches and only the third splits on a cardinal. Basis: agents/tasks/LJ-1-437/Probe437.agda:305
3. The finite branch is closed by the motive's own hypothesis, and the `ω` branch by the chapter's `squareω`. Basis: agents/tasks/LJ-1-437/Probe437.agda:307
4. The band membership yields the ordinal certificate the motive wants. Basis: agents/tasks/LJ-1-437/Probe437.agda:284
5. `[LJ-1.447]` delivers the third branch as DATA under one named residue. Basis: agents/tasks/LJ-1-447/LJ-1.447.md:9
6. The consumer of this family is `[LJ-1.434]`'s `SqFam`, and it wants DATA. Basis: agents/tasks/LJ-1-434/Probe434.agda:44
7. `[LJ-1.434]` is GO on the consumer under a TRUNCATED family, and the gap between the two is stated there and not inhabited. Basis: agents/tasks/LJ-1-434/Probe434.agda:56
8. The chapter that consumes the family takes it as a module parameter and spends it in two places. Basis: src/L/BoundedSubset.lagda.md:1388
9. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
10. The architecture is a CANDIDATE and only a measurement settles it. Basis: dev/pod/screen.toml:10
11. `make check` is the gate before any commit. Basis: AGENTS.md:75
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THE RECURSION IS WRITTEN AND GREEN.** `agents/tasks/LJ-1-437/Probe437.agda`
runs the `∈`-induction over the band at the motive `Goal x = IsOrd x → infinite
x → ∥ sq x ∥₁` (`:298-348`). Two of its three branches carry no truncation of
their own: the finite branch is `Empty.rec` and the `ω` branch is `squareω`.
The `∣_∣₁` in each is put there by the motive and by nothing else.

**THE THIRD BRANCH IS THE ONLY ONE THAT NEEDED THE TRUNCATION**, because it
spent the ambient arrow, which arrives truncated
(`agents/tasks/LJ-1-437/Probe437.agda:334-341`).

## WHAT IS MISSING

The same recursion at the UNTRUNCATED motive. Nobody has run it, because until
`[LJ-1.447]` no task could supply the third branch as data.

## THE REASONING

**WHY THIS IS THE TASK THAT DECIDES THE COUNTING LEG.** The consumer needs the
family as DATA (`src/L/BoundedSubset.lagda.md:1388-1390`). `[LJ-1.435]` and
`[LJ-1.436]` each measured a route that would let a TRUNCATED family through
the chapter, and each returned NO-GO. So the family must arrive untruncated,
and this term is where that happens or does not.

**D-10, BEFORE ANY AGDA.** Write the two motives side by side:

    Goal437 x = IsOrd x → (⟨ x ∈ ω ⟩ → Empty.⊥) → ∥ sq x ∥₁
    Goal448 x = IsOrd x → (⟨ x ∈ ω ⟩ → Empty.⊥) → sq x

Say in one line which branches of `Probe437.agda:305-310` change and which do
not. If more than the third branch changes, the plan below is wrong and the
report says so.

**THE SHAPE.**

1. Copy the imports, `band-ord` (`Probe437.agda:284-288`) and the `ord-tri`
   split (`:305-310`) from `Probe437.agda`. Do not import a probe.
2. Take `descent-both` as a MODULE HYPOTHESIS at `[LJ-1.447]`'s delivered type,
   with its `residue` parameter carried at the module level. **Do not rebuild
   either seal and do not restate the four cases.** This file holds no `κL` and
   no `κC`.
3. Do W3 first, then the obligation.

**THE INDUCTION HYPOTHESIS CHANGES SHAPE AND YOU MUST WATCH IT.** `[LJ-1.447]`
takes its induction hypothesis with the arguments in the order
`(y) → ⟨ y ∈ˢ x ⟩ → IsOrd y → infinite y → sq y`
(`agents/tasks/LJ-1-432/Probe432.agda:159`), while `∈-induction` supplies
`(y) → ⟨ y ∈ x ⟩ → Goal y` and `Goal` takes the certificate first
(`Probe437.agda:298`). **Adapt at the call site with a lambda and report the
adapter.** If the two cannot be adapted without a `subst`, that is a finding.

**REQUIRED REPORT SECTION `## DOES IT MEET THE CONSUMER`.** State, as types and
at `file:line`, `sq-data-closed` and `[LJ-1.434]`'s `SqFam`
(`agents/tasks/LJ-1-434/Probe434.agda:44-48`). One quantifies `(δ : V ℓ)` and
reads membership as `∈`; the other quantifies `(δ : S)` and reads it as `∈ˢ`.
**Write the adapter as a plain function, typecheck it, and report whether it is
the identity.** If it is, the counting leg's consumer is fed under one
hypothesis and you say exactly that. If it is not, name the repackaging and do
NOT hide it inside a `subst`.

**DO NOT CLAIM THE TROPHY AND DO NOT CLAIM THE CAMPAIGN CLOSES.** The
conclusion holds under `residue`, which nothing in this tree proves. The trophy
case is `src/Landmarks.lagda.md` and this task does not touch it.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 120 lines in the probe, of which the obligation
and its recursion are about 30. BASIS: `agents/tasks/LJ-1-437/Probe437.agda`
spends 66 lines on the recursion INCLUDING the cardinal split this file does
not carry, and `agents/tasks/LJ-1-420/Probe420.agda` is 99 lines for an
assembly of this class. Comparables are of SHAPE, and nothing may be funded
against them.

## W3, THE WIDEST UNMEASURED TERM

It is the `ω` branch, because it is the one place where the truncation was NOT
put there by the arrow.

    omega-branch : (x : V ℓ) → x ≡ ω → sq x
    omega-branch x x≡ω = subst sq (sym x≡ω) squareω

**Write it FIRST, with the obligation omitted, and typecheck it ALONE.**
`squareω` comes from `L.InjChain` (`agents/tasks/LJ-1-437/Probe437.agda:51`)
and `Probe437.agda:308` uses it under `∣_∣₁`. **If `squareω` is itself
truncated, this branch cannot be untruncated, the plan fails at its cheapest
point, and the whole task stops there.** That is a one-line measurement of the
task's own premise and it must run before anything else.

ESTIMATE for W3: two lines and under 3 seconds. BASIS: `Probe437.agda:308` is
the same line with one `∣_∣₁` around it. If `squareω` is truncated, say so at
`file:line`; that is the finding and it is worth more than the obligation.

Report the median wall time and the peak RSS over three forced rechecks at the
pane's caliber, for W3 alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO PUTS THE COUNTING LEG'S SUPPLY HALF IN DATA FORM, UNDER ONE NAMED
HYPOTHESIS.** With `[LJ-1.434]`'s consumer it says: the bounded-subset lemma's
conclusion follows from `residue` alone. That is one type for `[LJ-2.5]` to
rule on, and it replaces `SqCollect`, which asks for a choice principle, with a
statement about two ordinals.

**A NO-GO IS WORTH AS MUCH.** It says the truncation in `[LJ-1.437]` was not
only the arrow's: the `ω` branch, or `squareω`, or the adapter carries one too.
Then the truncated route is not an artefact of one hypothesis, and `[LJ-2.5]`
must be told that.

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
# A D-10 STOP RUNS NO AGDA, SO IT EXITS 0 AND MATCHES NO exit_code 42 BRANCH.
# `[LJ-1.440]` parked `no-match` seven times for exactly this gap
# (dev/pod/transitions/2026-08.jsonl:832). A stated NO-GO is the critic's
# input and never a close, so this routes to the critic and the critic's
# return closes the task.
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-448/review-of-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-448/Probe448.agda"]
  changed_files_none = ["agents/tasks/LJ-1-448/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-448/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 213.801)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 201.418)
- CANDIDATE archive/dev/JOURNAL.md  (score 195.606)
- CANDIDATE dev/ARCHIVE.md  (score 162.613)
- CANDIDATE archive/dev/DD-archived.md  (score 162.493)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 67.435)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 66.441)
- CANDIDATE dev/literature/digest.md  (score 48.843)
- CANDIDATE dev/literature/terms-2026-08.md  (score 36.316)
- CANDIDATE dev/literature/geology.md  (score 34.518)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
