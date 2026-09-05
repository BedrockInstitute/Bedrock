# LJ-1.446: the coded least cardinal is not below the ambient one

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-446/Probe446.agda`:

    kappaC-not-below :
        (a : S) (oa : IsOrd (fst a))
      → ⟨ fst (κC a oa) ∈ˢ fst (κL a oa) ⟩ → Empty.⊥

`κL` is the sealed ambient least cardinal, five projections, at
`agents/tasks/LJ-1-437/Probe437.agda:90-107`. `κC` is the CODED selection at
`agents/tasks/LJ-1-431/Probe431.agda:126-134`. Land nothing in `src/`.

**THE PROOF IS ONE APPLICATION AND THE BRIEF SAYS SO UP FRONT.** Feed the
coded arrow to the ambient minimality:

    κ-min-atL a oa (κC a oa) κC∈κL ∣ arrow-at-kappaC ∣₁

`κ-min-atL` is projection five of the seal (`Probe437.agda:104-107`), whose
type is `κ-min-at` at `src/L/Cardinal.lagda.md:140-141`. `arrow-at-kappaC` is
`[LJ-1.431]`'s delivered term (`Probe431.agda:133-134`), and it is DATA, so
`∣_∣₁` is the only step between them. **The work of this task is not the
application. It is making the two sites meet, and that is W3 below.**

**READ THREE REPORTS BEFORE ANY AGDA, AND STOP IF ANY VERDICT IS NOT `GO`:**
`agents/tasks/LJ-1-431/lj-1.431-report.md` (`:27`),
`agents/tasks/LJ-1-438/lj-1.438-report.md` (`:73`) and
`agents/tasks/LJ-1-430/lj-1.430-report.md` (`:81`). Quote each verdict line and
each delivered type before you write a line of Agda.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-446/Probe446.agda::kappaC-not-below"]

## SCOPE (write)
- agents/tasks/LJ-1-446/Probe446.agda
- agents/tasks/LJ-1-446/lj-1.446-report.md
- agents/tasks/LJ-1-446/review-of-kappaC-not-below.md
- agents/tasks/LJ-1-446/runs/

## PREMISES

1. `[LJ-1.431]` is GO on the arrow as DATA at the coded selection. Basis: agents/tasks/LJ-1-431/lj-1.431-report.md:27
2. Its delivered term is `arrow-at-kappaC`, generic in `a`. Basis: agents/tasks/LJ-1-431/Probe431.agda:133
3. `[LJ-1.438]` is GO on the nonemptiness that the coded selection needs. Basis: agents/tasks/LJ-1-438/lj-1.438-report.md:73
4. Its delivered term is `coded-nonempty` at a GENERIC L-element. Basis: agents/tasks/LJ-1-438/Probe438.agda:128
5. `[LJ-1.430]` is GO on the coded selection and on the ordinality of its value. Basis: agents/tasks/LJ-1-430/lj-1.430-report.md:81
6. The ambient minimality fires on a TRUNCATED ambient injection and asks for no code. Basis: src/L/Cardinal.lagda.md:140
7. The five-projection seal carries that minimality as `κ-min-atL`. Basis: agents/tasks/LJ-1-437/Probe437.agda:104
8. The seal is a measured cure and its own probe names the wall it answers. Basis: agents/tasks/LJ-1-437/Probe437.agda:83
9. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
10. A measured cure does not transfer by analogy; re-measure it at its own site. Basis: dev/LESSONS.md:3752
11. The architecture is a CANDIDATE and only a measurement settles it. Basis: dev/pod/screen.toml:10
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THIS CAMPAIGN CARRIES TWO LEAST CARDINALS AND NO RELATION BETWEEN THEM.**

- The AMBIENT one, `κL`: the least ordinal in `sucV (fst a)` that `fst a`
  injects into, with the injection TRUNCATED
  (`src/L/Cardinal.lagda.md:133`), and with a minimality that fires on a
  truncated ambient injection (`:140`).
- The CODED one, `κC`: the least ordinal in the same carrier that `a` injects
  into THROUGH A CODE (`agents/tasks/LJ-1-430/Probe430.agda:82-90`), whose
  arrow is DATA (`agents/tasks/LJ-1-431/Probe431.agda:133-134`) and whose
  ordinality is delivered (`Probe430.agda:96-98`).

Every task from `[LJ-1.424]` to `[LJ-1.438]` worked at one of the two. **No
term in this tree says which is larger.**

## WHAT IS MISSING

The one relation that is UNCONDITIONAL. `κL ≤ κC` costs one application,
because a code yields an ambient injection and the ambient site is minimal over
exactly those. The other direction is not this task and the brief does not
attempt it.

## THE REASONING

**WHY THIS IS WORTH A DISPATCH AND IS NOT BOOKKEEPING.** The campaign's two
open routes are dual. At `κL` the minimality is ambient, so case 3 of the
`[LJ-1.421]` split closes (`agents/tasks/LJ-1-406/Probe406.agda:180-190`), and
case 4 is blocked because the arrow is truncated. At `κC` the arrow is data, so
case 4 closes (`agents/tasks/LJ-1-432/Probe432.agda:155-168`), and case 3 is
blocked because the minimality fires only on a code
(`agents/tasks/LJ-1-432/lj-1.432-report.md:180-231`). **A route that joins the
two halves needs to know how the two ordinals sit.** This term is the half of
that relation that costs nothing, and it must be in the tree before any brief
reasons about the other half.

**D-10, BEFORE ANY AGDA.** Write down, as types, the two selections side by
side: `InjP'` at `src/L/Cardinal.lagda.md:82-83` and `CodedInjP'` at
`agents/tasks/LJ-1-431/Probe431.agda:119-121`. Say in one line whether they
range over the SAME carrier `⟪ sucV (fst a) ⟫`. If they do not, the ordering
question is not the question this brief asks, and that is a STOP.

**THE SHAPE.**

1. Rebuild the five-projection seal exactly as `Probe437.agda:90-107` carries
   it. Do not import a probe.
2. Rebuild the coded selection exactly as `Probe431.agda:100-134` carries it,
   with `nonempty-coded` as a MODULE HYPOTHESIS.
3. Do W3 first, then the obligation, then the report.

**`nonempty-coded` IS A HYPOTHESIS HERE AND `[LJ-1.438]` IS ITS PAYER.** Do not
inhabit it in this file. Name it in a section `## WHO OWES WHAT`, with the
payer's report line and the payer's delivered type. If the two types do not
agree, say so; that is the W3 finding and it is worth more than the obligation.

**DO NOT CLAIM MORE THAN THE TERM SAYS.** `kappaC-not-below` says the coded
least cardinal is not STRICTLY below the ambient one. It does NOT say the two
are equal, and it does not say the coded route closes. **Do not write the word
`impossible` about any statement this task does not refute.** Audit finding F5
measured that inflation once (`dev/pod/audit-2026-08-20.md:76`).

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 150 lines in the probe, of which the obligation is
about 6. BASIS: `agents/tasks/LJ-1-431/Probe431.agda` is 134 lines and holds
the selection and the arrow this file rebuilds; the seal at
`Probe437.agda:90-107` is 18 lines. Comparables are of SHAPE, and nothing may
be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is whether `[LJ-1.438]`'s payment PLUGS INTO `[LJ-1.431]`'s selection, or
whether the two files spell the same predicate two ways.

    plug : ∥ Σ[ d ∈ ⟪ sucV (fst a) ⟫ ] ⟨ CodedInjP' d ⟩ ∥₁
    plug = coded-nonempty

**Write it as that one line, with `coded-nonempty` as a module hypothesis at
`[LJ-1.438]`'s DELIVERED type (`Probe438.agda:128-131`), typecheck it ALONE
with the obligation omitted, and report the result.** `[LJ-1.438]` rebuilds
`γ` from `[LJ-1.429]` and `upα` from `[LJ-1.430]`; `[LJ-1.431]` rebuilds them
too. If the two rebuilds differ in one index, the payment does not plug in, and
three green returns rest on a join nobody has run. **The elaborator's error at
`file:line` IS the finding.**

ESTIMATE for W3: one line, under 2 seconds on top of the file's own cost.
BASIS: it is an identity between two spellings of one truncated existence, and
`[LJ-1.443]`'s brief asks the same class of question at the other end of the
campaign. If it costs more, say so.

Report the median wall time and the peak RSS over three forced rechecks at the
pane's caliber.

## WHAT GO AND NO-GO EACH EARN

**A GO PUTS THE FIRST RELATION BETWEEN THE TWO ROUTES IN THE TREE.** It says
the coded cardinal sits at or above the ambient one, so any statement that the
two coincide is a statement about ONE remaining direction, and the campaign can
name that direction instead of describing it.

**A NO-GO IS WORTH MORE.** The likely NO-GO is the W3 one: the two rebuilds do
not meet. That is a defect in how this campaign has stated its own selection
across five tasks, and it must be found before another brief stands on them.

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
  changed_files_any = ["agents/tasks/LJ-1-446/review-of-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-446/Probe446.agda"]
  changed_files_none = ["agents/tasks/LJ-1-446/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-446/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 173.253)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 170.936)
- CANDIDATE archive/dev/JOURNAL.md  (score 143.704)
- CANDIDATE dev/ARCHIVE.md  (score 125.393)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 117.549)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 51.257)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 49.630)
- CANDIDATE dev/literature/terms-2026-08.md  (score 38.273)
- CANDIDATE dev/literature/digest.md  (score 30.960)
- CANDIDATE dev/literature/geology.md  (score 24.554)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
