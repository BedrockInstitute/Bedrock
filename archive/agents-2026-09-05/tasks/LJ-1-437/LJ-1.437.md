# LJ-1.437: the truncated square law with NO hypothesis

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-437/Probe437.agda`, in a module whose
parameters are `{ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (α₀ : V ℓ) (oα₀ : IsOrd α₀)`
and NOTHING else:

    sq-trunc-closed :
        (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
      → ∥ sq δ ∥₁

**THE FILE CARRIES NO MODULE HYPOTHESIS AT ALL.** That is the whole point of
this task. `[LJ-1.407]` delivered this exact type under ONE bare hypothesis
(`agents/tasks/LJ-1-407/Probe407.agda:203-210`), and `[LJ-1.406]` delivered
that hypothesis (`agents/tasks/LJ-1-406/Probe406.agda:180-190`). Nobody has
put the two in one file. Until somebody does, the campaign has two green
probes and no closed statement.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-437/Probe437.agda::sq-trunc-closed"]

## SCOPE (write)
- agents/tasks/LJ-1-437/Probe437.agda
- agents/tasks/LJ-1-437/lj-1.437-report.md
- agents/tasks/LJ-1-437/review-of-sq-trunc-closed.md

## PREMISES
- `[LJ-1.407]` is GO and it delivers the target type under one bare hypothesis. Basis: agents/tasks/LJ-1-407/lj-1.407-report.md:18
- That delivered term is `sq-trunc`, and it is an `∈-induction` at the motive `Goal`. Basis: agents/tasks/LJ-1-407/Probe407.agda:262
- Its ONE hypothesis is `init-at-kappa`, taken bare and never inhabited there. Basis: agents/tasks/LJ-1-407/Probe407.agda:203
- `[LJ-1.406]` is GO and it inhabits that hypothesis. Basis: agents/tasks/LJ-1-406/lj-1.406-report.md:13
- The inhabitant is `init-at-kappa`, and its conjunct 4 closes from a truncated `∥ sq β ∥₁` and a truncated arrow. Basis: agents/tasks/LJ-1-406/Probe406.agda:180
- `[LJ-1.406]` seals the ambient least cardinal at FOUR projections, and one of them is the minimality. Basis: agents/tasks/LJ-1-406/Probe406.agda:81
- `[LJ-1.407]` seals the same atom at four projections, and one of them is the successor membership. Basis: agents/tasks/LJ-1-407/Probe407.agda:98
- `sq` and `Init` are the chapter's own, and this probe imports them. Basis: src/L/Ordinal/SquareLaw.lagda.md:685
- The chapter already exports the truncated form under `Init`. Basis: src/L/Ordinal/SquareLaw.lagda.md:963
- The consumer's module parameter is the UNtruncated Sigma today. Basis: src/L/StageCardinal.lagda.md:17
- The architecture is a CANDIDATE and only a measurement settles it. Basis: dev/pod/screen.toml:10

## WHAT IS DELIVERED ALREADY

**THE SUPPLIER IS GREEN.** `sq-trunc` (`agents/tasks/LJ-1-407/Probe407.agda:262-265`)
is an `∈-induction` over the band with four cases and no residue. Its report
records the descent case as a `PT.map2` over the truncated arrow and the
induction hypothesis (`agents/tasks/LJ-1-407/lj-1.407-report.md:81`), so
nothing in it untruncates anything.

**THE HYPOTHESIS IS GREEN.** `init-at-kappa`
(`agents/tasks/LJ-1-406/Probe406.agda:180-190`) returns `Init (fst (κL a oa))`
from `⟨ ω ∈ˢ fst (κL a oa) ⟩` and a truncated induction hypothesis. The two
types are written the same way, projection for projection.

**BOTH FILES SEAL THE SAME ATOM.** `[LJ-1.406]` seals `κL`, `κoL`, `κ-injL`
and `κ-min-atL` (`Probe406.agda:81-95`). `[LJ-1.407]` seals `κL`, `κoL`,
`κ∈sucL` and `κ-injL` (`Probe407.agda:98-109`). The union is FIVE projections
of one `LeastCardInjL` application.

## WHAT IS MISSING

**ONE FILE.** No file in the tree states the truncated square law over the band
with an empty hypothesis telescope. The join has never been run, so nobody has
measured whether one shared `opaque` block carries both proofs.

This matters beyond tidiness. A brief that wants to land the truncated square
law in `src/` cannot cite two probes and a hypothesis: it must cite ONE term
whose telescope is empty. This task produces that term.

## THE REASONING

**D-10, BEFORE ANY AGDA.** Write in the report, at `file:line`, the type of
`[LJ-1.407]`'s bare hypothesis (`Probe407.agda:203-210`) and the type of
`[LJ-1.406]`'s obligation (`Probe406.agda:180-190`), and say whether they are
the same type, projection for projection. **If they differ, say where, and
STOP.** Do not repair a mismatch by weakening either type. A mismatch is a
full return: it says two GO reports do not join, and the campaign has been
reading them as if they did.

**THE SHAPE, AND IT IS A JOIN AND NOT A NEW PROOF.**

1. One module header, with `α₀` and `oα₀` as `[LJ-1.407]` has them
   (`Probe407.agda:32-33`), and no hypothesis module below it.
2. ONE `opaque` block, carrying the FIVE projections that the two files seal
   between them: `κL`, `κoL`, `κ∈sucL`, `κ-injL`, `κ-min-atL`.
3. `[LJ-1.406]`'s helpers and `clause4-at-kappa`, then `init-at-kappa` as a
   DEFINITION and not a parameter.
4. `[LJ-1.407]`'s `Goal`, `step` and `sq-trunc`, with the hypothesis module
   header at `Probe407.agda:203-210` deleted and its name now resolving to the
   definition from step 3.

**REBUILD, DO NOT IMPORT.** Do not import `LJ-1-406.Probe406` or
`LJ-1-407.Probe407`. A probe is not a library. Copy the text you need into
`Probe437.agda` and say in the report which lines you copied.

**W2 (DD4).** The module stays generic in `ℓ` and in `α₀`. Name no numeral and
no site. `ω` appears only where the two predecessors already put it.

**W3, THE WIDEST UNMEASURED TERM.** It is the SHARED SEAL, and nothing else in
this task is unmeasured:

    init-at-kappa :
        (a : S) (oa : IsOrd (fst a))
      → ⟨ ω ∈ˢ fst (κL a oa) ⟩
      → ((β : V ℓ) → IsOrd β → ⟨ β ∈ˢ fst (κL a oa) ⟩
           → (⟨ β ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq β ∥₁)
      → Init (fst (κL a oa))

**THE PROBE.** Write the file down to `init-at-kappa` and STOP. Typecheck it
with `Goal`, `step` and `sq-trunc-closed` OMITTED. This is the one step that
can fail: `[LJ-1.406]` proved this term against a seal of four projections
that did NOT include `κ∈sucL`, and `[LJ-1.407]` proved its own cases against a
seal of four that did NOT include `κ-min-atL`. A single block carries all five,
and the elaborator has never seen that block. Report wall seconds and peak RSS
at the caliber the program set on your pane, one Agda process, three forced
rechecks, and the median. Quote the elaborator at `file:line` if it refuses.
A heap event is a WALL event: report it and stop.

**MEASURE THE JOINED FILE, NOT ONLY THE OBLIGATION.** `[LJ-1.406]` measured a
median of 1.80 s at 117 code lines and `[LJ-1.407]` a median of 1.77 s at 176.
Report the joined file's median and peak RSS. The next brief prices a `src/`
landing against that number, so it must be measured and not estimated.

**C-42.** In a section `## WHAT THIS DOES NOT MEASURE`, say plainly that this
task closes the SUPPLY of the truncated square law and measures nothing about
the CONSUMER. Name at `file:line` the consumer's module parameter
(`src/L/StageCardinal.lagda.md:17-20`), which is untruncated today, and say
that `[LJ-1.434]`, `[LJ-1.435]` and `[LJ-1.436]` are the tasks that measure it.
**Do not open those three tasks, do not import their probes, and do not copy a
type out of their briefs.**

ESTIMATE for the Agda: about 240 code lines. BASIS: two delivered comparables
of SHAPE, `agents/tasks/LJ-1-406/Probe406.agda` at 117 non-blank non-comment
lines and `agents/tasks/LJ-1-407/Probe407.agda` at 176, less the preamble and
the small helpers that both carry. **Comparables of SHAPE and never of size,
and nothing may be funded against them.**

## WHAT GO AND NO-GO EACH EARN

**A GO CLOSES THE SUPPLY SIDE.** It says the truncated square law holds at
every infinite band ordinal with an EMPTY hypothesis telescope. Say in the
report, in one sentence with a `file:line`, what the term's telescope is, so
the next brief can quote it without opening the probe.

**A NO-GO IS WORTH AS MUCH.** It says the two GO reports do not join, and it
names the projection or the seal that refuses. That is a measured fact about
two returns the campaign has treated as composable for a fortnight.

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
  changed_files_any = ["agents/tasks/LJ-1-437/Probe437.agda"]
  changed_files_none = ["agents/tasks/LJ-1-437/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-437/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 205.063)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 176.189)
- CANDIDATE archive/dev/JOURNAL.md  (score 174.083)
- CANDIDATE dev/ARCHIVE.md  (score 153.374)
- CANDIDATE archive/dev/ORCHESTRATION.md  (score 122.573)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 78.284)
- CANDIDATE dev/literature/terms-2026-08.md  (score 47.727)
- CANDIDATE dev/literature/devlin-II5.md  (score 45.964)
- CANDIDATE dev/literature/digest.md  (score 35.119)
- CANDIDATE dev/literature/geology.md  (score 32.855)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
