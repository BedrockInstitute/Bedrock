# LJ-1.427: run the descent at the INTERNAL least cardinal, not the ambient one

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-427/Probe427.agda`, at a GENERIC ordinal:

    descent-from-internal :
        (x : V ℓ) → IsOrd x → ⟨ ω ∈ˢ x ⟩
      → ((y : V ℓ) → ⟨ y ∈ˢ x ⟩ → IsOrd y → (⟨ y ∈ˢ ω ⟩ → Empty.⊥) → sq y)
      → sq x

**THAT IS `[LJ-1.421]`'s STATEMENT, WORD FOR WORD, WITH ONE THING CHANGED: the
descent target is the INTERNAL least cardinal `δᴸ` (`src/L/Cardinal.lagda.md:253`)
and not the ambient `κL`.**

**THE TELESCOPE MUST NOT HOLD `kappa-arrow-data`.** That hypothesis is the whole
reason for this task. It must not hold `amb-to-coded`, `coded-descent` or
`IsCardinalL` either.

## THE HYPOTHESES, AND WHERE THEIR TYPES COME FROM

Take these as module parameters, at the types their REPORTS record, never their
briefs:

- `coded-to-arrow`, `agents/tasks/LJ-1-424/lj-1.424-report.md`.
- `internal-nonempty`, `agents/tasks/LJ-1-425/lj-1.425-report.md`.

**IF EITHER REPORT IS NO-GO, OR NAMES ITS STATEMENT FALSE, DO NOT WRITE THAT
TYPE INTO THIS TELESCOPE.** Stop, say which report refused it, and return.
Owner's ruling, 2026-08-20, measured by `dev/pod/audit-2026-08-20.md` findings
F1 and F3.

**IF EITHER TASK HAS NOT RUN**, take its type from its own brief, say in the
report that you did so, and mark the return provisional. That is admissible; a
refuted type is not.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-427/Probe427.agda::descent-from-internal"]

## SCOPE (write)
- agents/tasks/LJ-1-427/Probe427.agda
- agents/tasks/LJ-1-427/lj-1.427-report.md
- agents/tasks/LJ-1-427/review-of-descent-from-internal.md

## PREMISES
- `[LJ-1.421]` delivered this statement with the AMBIENT least cardinal as the target, and returned GO. Basis: agents/tasks/LJ-1-421/lj-1.421-report.md:53
- Its one question-hypothesis was the ambient arrow as data. Basis: agents/tasks/LJ-1-421/Probe421.agda:214
- The induction splits on an ordinal trichotomy at the target. Basis: agents/tasks/LJ-1-421/Probe421.agda:182
- The other branch spends the target's infiniteness. Basis: agents/tasks/LJ-1-421/Probe421.agda:164
- The `Init` conjunct at the ambient target is delivered and spends the AMBIENT minimality. Basis: agents/tasks/LJ-1-406/Probe406.agda:180
- The internal least cardinal is delivered as an L-element. Basis: src/L/Cardinal.lagda.md:253
- Its witness is a coded injection, truncated, and it comes free with the module. Basis: src/L/Cardinal.lagda.md:257
- Its leastness is stated against the STAGE well-order, and not against membership on the ordinals. Basis: src/L/Cardinal.lagda.md:261
- Its predicate carries no ordinality conjunct, so a least member of the stage need not be an ordinal. Basis: src/L/Cardinal.lagda.md:239
- The consumer spends the pairing once, in the limit step. Basis: src/L/StageCardinal.lagda.md:283
- The consumer's output is the counting leg at every band ordinal. Basis: src/L/StageCardinal.lagda.md:564
- The architecture is a CANDIDATE and only a measurement settles it. Basis: dev/pod/screen.toml:10

## WHAT IS DELIVERED ALREADY

**THE WHOLE INDUCTION.** `agents/tasks/LJ-1-421/Probe421.agda:225-263` is this
statement at the ambient target, green, with the plumbing above it: the split
(`:182-204`) and the infiniteness step (`:164-183`). Reuse the SHAPE. Do not
import that file.

## WHAT IS MISSING

**A DESCENT TARGET WHOSE ARROW THE TREE CAN PRODUCE.** `[LJ-1.421]`'s target is
the ambient `κL`, whose arrow arrives truncated (`src/L/Cardinal.lagda.md:133`)
and whose untruncation `[LJ-1.422]` refused. The internal `δᴸ` arrives with a
CODED witness instead (`src/L/Cardinal.lagda.md:257`), and `[LJ-1.424]`
untruncates that shape. **So the question is not whether the arrow exists. It is
whether `δᴸ` can stand where `κL` stood.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE POINT OF THIS TASK.** `κL` is an ordinal
by construction: it is a member of `sucV (fst a)` and inherits ordinality
(`src/L/Cardinal.lagda.md:125-127`). **`δᴸ` is a member of `Lset β` and nothing
in `InternalLeastCard.Good` (`src/L/Cardinal.lagda.md:239-240`) asks it to be an
ordinal.** The induction needs an ordinal at that position twice: the
trichotomy split (`agents/tasks/LJ-1-421/Probe421.agda:182-185`) and the `Init`
conjunct (`agents/tasks/LJ-1-406/Probe406.agda:180-190`). **Settle that before
anything else.**

**DO NOT SMUGGLE IN AN ORDINALITY HYPOTHESIS TO MAKE THE TERM GREEN.** If the
descent needs `Good` to carry an ordinality conjunct, say so, state the
corrected `Good` in the report, and say plainly that adding a conjunct changes
WHICH δ is least and therefore changes the object. **Write nothing into `src/`.**

**THE SECOND THING TO SETTLE, AND IT IS SEPARATE.** `init-at-kappa`
(`agents/tasks/LJ-1-406/Probe406.agda:180`) spends the AMBIENT minimality
`κ-min-atL` (`src/L/Cardinal.lagda.md:140`), which says no member of `κ` admits
the arrow. `δ-min` (`src/L/Cardinal.lagda.md:261`) says something else: no
member of `Lset β` BELOW δ in the stage order admits a code. **Say whether the
second gives the first, and if not, name exactly what is lost.**

**W2 (DD4).** Generic in `x`. Name no band, no cardinal and no numeral except
`ω`, which the statement's own type names.

**W3, THE WIDEST UNMEASURED TERM.**

    delta-is-ordinal

**THE PROBE.** Typecheck `IsOrd (fst δᴸ)` ALONE, as an obligation with
`internal-nonempty` as a bare module hypothesis and nothing else built. This is
two lines and it is the cheapest kill in this task: if `δᴸ` is not an ordinal,
the whole swap closes in ONE dispatch and the report says which of the two uses
above breaks. Report wall seconds and peak RSS at the caliber the program set on
your pane, one Agda process, three forced rechecks, and the median. If it costs
a heap event, that is a WALL event: report it and stop.

ESTIMATE for the Agda: about 45 code lines. BASIS: `agents/tasks/LJ-1-421/Probe421.agda:225-263`
is the same induction in 39 lines, and this is that file with the descent target
swapped and its plumbing restated. **Comparables of SHAPE and never of size, and
nothing may be funded against them.**

**CLOSE WITH THE CAMPAIGN'S BILL, IN ONE SECTION.** Write
`## WHAT LJ-1 STILL OWES` and state, each with `file:line`: every hypothesis
`descent-from-internal` carries, whether each is delivered green somewhere in
`agents/tasks/` or in `src/`, and what remains before the counting leg could be
written into `src/`.

## WHAT GO AND NO-GO EACH EARN

**A GO IS THE CAMPAIGN'S RESULT.** The descent then runs with no ambient
untruncation anywhere, and `[LJ-1.423]`'s second hypothesis
(`kappa-arrow-data`) disappears rather than being paid. Name in the report the
exact line of `src/L/StageCardinal.lagda.md` a later task would change, and what
a `src/` landing would cost.

**A NO-GO IS WORTH AS MUCH.** It names the property the AMBIENT least cardinal
carries that the INTERNAL one does not, at `file:line`. That is a statement
about the two-tower candidate itself and it is a first-class input to
`[LJ-2.5]`. **Do not write a universal negative**: audit findings F5 and F6
record two reports that turned「this attempt failed」into「impossible」
(`dev/pod/audit-2026-08-20.md:76` and `:83`).

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
  changed_files_any = ["agents/tasks/LJ-1-427/Probe427.agda"]
  changed_files_none = ["agents/tasks/LJ-1-427/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-427/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 204.543)
- CANDIDATE archive/dev/JOURNAL.md  (score 194.216)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 177.234)
- CANDIDATE archive/dev/DD-archived.md  (score 162.392)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 161.519)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 64.467)
- CANDIDATE dev/literature/devlin-II5.md  (score 48.441)
- CANDIDATE dev/literature/terms-2026-08.md  (score 43.403)
- CANDIDATE dev/literature/digest.md  (score 40.921)
- CANDIDATE dev/literature/geology.md  (score 40.361)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
