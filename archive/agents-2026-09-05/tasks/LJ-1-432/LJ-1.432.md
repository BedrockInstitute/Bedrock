# LJ-1.432: which case of the descent a coded arrow closes, and which it does not

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-432/Probe432.agda`, at a GENERIC ordinal:

    descent-case4-coded :
        (x : V ℓ) (ox : IsOrd x) → ⟨ ω ∈ˢ x ⟩
      → ⟨ fst (κC (x , isL-ord x ox) ox) ∈ˢ x ⟩
      → ((y : V ℓ) → ⟨ y ∈ˢ x ⟩ → IsOrd y → (⟨ y ∈ˢ ω ⟩ → Empty.⊥) → sq y)
      → sq x

`κC` is a SEALED module hypothesis with three properties and nothing else, in
the shape `[LJ-1.421]` seals `κL` at `agents/tasks/LJ-1-421/Probe421.agda:125-135`:

    κC       : (a : S) (oa : IsOrd (fst a)) → S
    κC-ord   : IsOrd (fst (κC a oa))
    κC∈suc   : ⟨ fst (κC a oa) ∈ sucV (fst a) ⟩
    κC-arrow : ⟪ fst a ⟫ ↪ ⟪ fst (κC a oa) ⟫

**THE ARROW ARRIVES AS DATA AND NOT TRUNCATED. THAT IS THE ONLY DIFFERENCE FROM
`[LJ-1.421]`, AND THIS TASK MEASURES WHAT IT BUYS.**

**A REQUIRED REPORT SECTION, `## THE CASE THAT DOES NOT CLOSE`.** Name, at
`file:line`, what the OTHER case of the split costs when `κC` replaces `κL`:
`fst κC ≡ x`, where `[LJ-1.421]` closes through `init-at-kappa` and conjunct 4
spends `κ-min-at`. State whether that conjunct still closes when the selection's
minimality forbids a CODE rather than an ambient injection. **Do not build it.
Report it.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-432/Probe432.agda::descent-case4-coded"]

## SCOPE (write)
- agents/tasks/LJ-1-432/Probe432.agda
- agents/tasks/LJ-1-432/lj-1.432-report.md
- agents/tasks/LJ-1-432/review-of-descent-case4-coded.md

## PREMISES
- `descent-data` is GENERIC in its second set `d`, and nothing in its type names a least cardinal. Basis: agents/tasks/LJ-1-421/Probe421.agda:111
- `[LJ-1.421]` fixes `d := κL` only at the application, in one line. Basis: agents/tasks/LJ-1-421/Probe421.agda:150
- That task returned GO, and its report is in this tree. Basis: agents/tasks/LJ-1-421/lj-1.421-report.md:53
- It names the campaign's residue as ONE untruncated arrow at a named ordinal. Basis: agents/tasks/LJ-1-421/lj-1.421-report.md:60
- Case 4 of its split is where the untruncated arrow is spent, and it is spent ONCE. Basis: agents/tasks/LJ-1-421/Probe421.agda:257
- Case 3 of its split is paid already, from the TRUNCATED arrow, through `init-at-kappa`. Basis: agents/tasks/LJ-1-421/Probe421.agda:248
- `Init`'s fourth conjunct refutes an injection of the index into an infinite member's square. Basis: src/L/Ordinal/SquareLaw.lagda.md:696
- `[LJ-1.406]` pays that conjunct from the TRUNCATED arrow and from ambient minimality. Basis: agents/tasks/LJ-1-406/Probe406.agda:103
- The ambient minimality it spends forbids an ambient truncated injection into a member of the cardinal. Basis: src/L/Cardinal.lagda.md:140
- `sq` is a Sigma and not a truncation, which is why the arrow must be data. Basis: src/L/Ordinal/SquareLaw.lagda.md:685
- The infinitude of the target is a separate fact and `[LJ-1.421]` proves it from the truncated arrow. Basis: agents/tasks/LJ-1-421/Probe421.agda:164
- The split itself is by trichotomy on the selected ordinal against `x`. Basis: agents/tasks/LJ-1-421/Probe421.agda:182
- The architecture is a CANDIDATE and only a measurement settles it. Basis: dev/pod/screen.toml:10

## WHAT IS DELIVERED ALREADY

**THE DESCENT STEP, AND IT NEVER NAMED A LEAST CARDINAL.**
`descent-data : (x d : S) (ox : IsOrd (fst x)) → ⟨ fst d ∈ˢ fst x ⟩ → ⟪ fst x ⟫ ↪ ⟪ fst d ⟫ → sq (fst d) → sq (fst x)`
(`agents/tasks/LJ-1-421/Probe421.agda:111-118`) is generic in `d`. `[LJ-1.421]`
fixes `d := κL` in ONE line, at `:150`, and that is a choice of the application
and not of the lemma.

**CASE 3 OF THE SPLIT IS ALREADY PAID FROM A TRUNCATED ARROW.**
`agents/tasks/LJ-1-421/Probe421.agda:248-251` closes `fst κ ≡ x` through
`init-at-kappa`, whose fourth conjunct
(`agents/tasks/LJ-1-406/Probe406.agda:103-121`) consumes
`∥ ⟪ fst a ⟫ ↪ ⟪ fst κ ⟫ ∥₁` and never the data form.

## WHAT IS MISSING

**THE MEASUREMENT OF WHAT A DIFFERENT `d` BUYS.** Every attempt of this campaign
took `d := κL` and then tried to untruncate the ambient arrow at that one
ordinal. **Nobody has asked what happens when `d` is a different ordinal whose
arrow is data by construction.** This task asks exactly that, and it asks it for
ONE case of the split, because that is the case where the data arrow is spent
(`agents/tasks/LJ-1-421/Probe421.agda:257`).

## THE REASONING

**D-10, BEFORE ANY AGDA.** Read `agents/tasks/LJ-1-421/Probe421.agda:225-263`
and write in the report, at `file:line`, which arguments of `descent-data` case 4
supplies and where each comes from. **Name the one that `[LJ-1.421]` could not
pay and say why this telescope pays it.** If you cannot state it, do not write
Agda.

**STEP ONE, W3, THE INFINITUDE.** The induction hypothesis applies at `κC` only
when `κC` is not a member of `ω`. `[LJ-1.421]` proves that at `κL` from the
TRUNCATED arrow (`Probe421.agda:164-180`). **Restate it at `κC` from the DATA
arrow.** Typecheck it ALONE.

**STEP TWO, THE OBLIGATION.** Apply `descent-data` with `d := κC`, the membership
from the hypothesis, the arrow from `κC-arrow`, and `sq (fst κC)` from the
induction hypothesis at `κC-ord` and step one. Rebuild `descent-data`,
`descent-core`, `mem-incl` and `comp-inj` from
`agents/tasks/LJ-1-421/Probe421.agda:62-118` rather than importing that probe.

**THE FOUR HYPOTHESES ARE OWED AND YOU DO NOT INHABIT ANY OF THEM.**
`[LJ-1.429]` owes the nonemptiness that makes `κC` exist, `[LJ-1.430]` owes
`κC-ord`, and `[LJ-1.431]` owes `κC-arrow`. **Do not import their probes, do not
copy a type out of any of their briefs, and do not assert any of their statements
as a fact anywhere in your report.** In a section `## WHO OWES WHAT`, name each
hypothesis, the task that owes it, and whether that task's REPORT is in your
tree today. **A report you cannot open is a report you may not cite.**

**DO NOT WRITE CASE 3 AND DO NOT WRITE THE FULL DESCENT.** They are not this
task's obligation, and a term that closes case 3 by adding a minimality
hypothesis would be exactly the shape audit findings F1 and F3 measured
(`dev/pod/audit-2026-08-20.md:34`). Report case 3 in prose and stop.

**W2 (DD4).** Generic in `x`. Name no cardinal, no band and no numeral. `ω`
appears only where `[LJ-1.421]`'s own statement puts it.

**W3, THE WIDEST UNMEASURED TERM.**

    kappaC-not-fin :
        (x : V ℓ) (ox : IsOrd x) → ⟨ ω ∈ˢ x ⟩
      → (⟨ fst (κC (x , isL-ord x ox) ox) ∈ˢ ω ⟩ → Empty.⊥)

**THE PROBE.** Typecheck `kappaC-not-fin` ALONE, with the obligation omitted,
before you write it. Report wall seconds and peak RSS at the caliber the program
set on your pane, one Agda process, three forced rechecks, and the median. **If
the infinitude does not close from the data arrow, the induction hypothesis
never reaches `κC`, and that is the NO-GO: it closes this route in ONE
dispatch.** Quote the elaborator at `file:line`. If it costs a heap event, that
is a WALL event: report it and stop.

ESTIMATE for the Agda: about 55 code lines. BASIS: `agents/tasks/LJ-1-421/Probe421.agda:62-118`
is the descent plumbing in 56 lines, and this is that block with the seal changed and
one application added. **Comparables of SHAPE and never of size, and nothing may be
funded against them.**

## WHAT GO AND NO-GO EACH EARN

**A GO SHRINKS THE CAMPAIGN'S RESIDUE AND DOES NOT DISCHARGE IT.** It says the
untruncated arrow the descent needs does NOT have to sit at the ambient least
cardinal, which is the object `[LJ-1.422]` refused. **Say plainly in the report
that case 3 is not closed**, and name in `## THE CASE THAT DOES NOT CLOSE` the
one statement that would close it, as a type, at `file:line`. That named type is
this task's real deliverable to `[LJ-2.5]`, and it is smaller than the residue
this campaign started with.

**A NO-GO IS WORTH AS MUCH.** It says the descent step is tied to the ambient
least cardinal after all, through the infinitude or through the membership, and
names which. That closes the whole coded line and hands `[LJ-2.5]` a measured
reason.

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
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-432/Probe432.agda"]
  changed_files_none = ["agents/tasks/LJ-1-432/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-432/review-of-*.md"]

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
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 137.261)
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 135.487)
- CANDIDATE archive/dev/JOURNAL.md  (score 115.217)
- CANDIDATE dev/ARCHIVE.md  (score 114.183)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 101.454)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 52.310)
- CANDIDATE dev/literature/devlin-II5.md  (score 43.740)
- CANDIDATE dev/literature/digest.md  (score 37.243)
- CANDIDATE dev/literature/geology.md  (score 36.890)
- CANDIDATE dev/literature/fine-structure.md  (score 26.712)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
