# LJ-1.386: internal existence of a pairing code at a band ordinal, GO or NO-GO

## HEAD
head_slot: mathematician
machine: shared

## THE OBLIGATION

Measure whether the delivered internal machinery can produce the internal
existence of a good pairing graph at ONE band ordinal. The probe file is
`agents/tasks/LJ-1-386/Probe386.agda`. It must state, at the band ordinal
`+ω ω` (`src/L/Ordinal/StageArith.lagda.md:41-42`), the proposition

    ∥ Σ[ A ∈ Mem (Lset β) ] ⟨ Good A ⟩ ∥₁

for the `Good` of `src/L/Cardinal.lagda.md:187-190`, and then either inhabit it
or state the obstruction that blocks it. **Both answers discharge this task.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-386/Probe386.agda::code-exists",
               "agents/tasks/LJ-1-386/Probe386.agda::code-inj"]

## SCOPE (write)
- agents/tasks/LJ-1-386/Probe386.agda
- agents/tasks/LJ-1-386/lj-1.386-report.md

## PREMISES
- `leastOf` turns the mere existence into DATA with no choice principle, so leg 2 costs nothing once leg 1 lands. Basis: src/L/Cardinal.lagda.md:194-195
- `small-inj` reads a coded injection out to an ambient injective function. Basis: src/L/Coding/Injection.lagda.md:147-151
- `+ω` is the named band candidate and its union representation is sealed, so a statement at `+ω ω` names an atom. Basis: src/L/Ordinal/StageArith.lagda.md:41-42
- Two of the route's three legs are delivered and only leg 1 is missing. Basis: agents/tasks/LJ-1-384/lj-1.384-report.md:58-74

## WHAT IS DELIVERED ALREADY
- `Good`, the predicate the code must satisfy: src/L/Cardinal.lagda.md:187-190
- `module Canonical`, leg 2, which selects the least code from the mere existence: src/L/Cardinal.lagda.md:182-204
- `module Small`, leg 3, which reads a code out to ambient data: src/L/Coding/Injection.lagda.md:123-151
- The read-back shape, already green in a sibling probe: agents/tasks/LJ-1-299/NoInj2.agda:107-110

## WHAT IS MISSING

Leg 1, the internal existence itself. It is internal cardinal arithmetic at the
band: the model's own statement that the band ordinal carries a pairing.
**Nothing in the tree states it today**, and `[LJ-1.384]` measured that no
dispatch has aimed at it (`agents/tasks/LJ-1-384/lj-1.384-report.md:74-76`).

## LAWS (program-generated, do not edit)

*The bundle `rules.py --for probe` emits. The kind is DERIVED from `## SCOPE (write)`, which names only `agents/tasks/LJ-1-386/`, and it is never declared. R17 and pre-flight P21.*

MANDATORY for kind `probe` (measures one thing and keeps the file as the report's other half. Gating, heap discipline, the transplant law, which is what a probe most often gets wrong, and the extent law, because a probe that refutes has measured ONE site.):

- **D-1. The probe doctrine**
  **Rule:** Before committing to a heavy or hard-to-reverse path, run the cheapest decisive probe with its abort criterion fixed in advance; a red verdict costs the attempt and nothing else.
  Full entry: dev/LESSONS.md:1064
- **P-l. A statement may be ABOUT a concrete stage without dragging that stage's PRESENTATION into its type**
  **The law.** Being about a concrete position is not what costs. Naming a transparent construction in a statement's TYPE is. If the tower's stage values are `opaque` upstream, a theorem may quantify over, hypothesize about and conclude at `Sset ω` freely, because the stage is an ATOM to the elaborator and nothing unfolds. If instead the type mentions a transparent presentation, such as `⟪ sucV (...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2343
- **P-i. The conversion-explosion playbook (imported from the source project)**
  **Rule:** When cubical Agda hangs or exhausts memory on this codebase family, the cause is one of three heavy-thing classes forced into normalization, and the cure is selected by the decision tree below, not by trial. Imported whole from the antecedent development's worklog (`../fol-reification/docs/WORKLOG.md` §5, twenty measured cases); read that section before any surgery on a hang.
  Full entry: dev/LESSONS.md:229
- **C-12. Agda runs under a hard heap cap; parallel writers under a quota**
  **Rule:** Every agda invocation runs under a GHC heap cap (`GHCRTS=-M<n>g`) so a runaway typecheck dies with a clean "Heap exhausted" exit instead of OOM-killing the machine; the orchestrator's audits run at `-M16g` and `make` exports a default. Sub-agent concurrency is TIERED (owner-widened 2026-08-02 once the caps and the watchdog were live): WIDE mode for routine batches, up to FOUR concurre...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2121
- **D-10. Price the truth of a recorded residue before pricing its proof**
  **Rule:** A residue recorded under the wall protocol names a TARGET, and a target can be false; before dispatching a discharge batch, spend the five minutes checking the target's truth at the intended generality (a Tarskian or cardinality obstruction is the usual killer), and record the corrected target beside the original.
  Full entry: dev/LESSONS.md:1361
- **C-22. A dispatched agent writes its deliverable incrementally, never at the end**
  **Rule:** When an agent's deliverable is a file, the brief must require it WRITTEN EARLY as a skeleton and filled incrementally, saving after each answer lands. An agent that researches for its whole budget and leaves the writing to the end returns nothing when the budget runs out, and its research dies with it. A partial dossier is a real deliverable; an unwritten perfect one is not.
  Full entry: dev/LESSONS.md:2283
- **R-40. A deep successor-chain membership witness normalizes super-linearly; climb by small closures**
  **Rule:** An ordinal-membership premise stated at a deep iterated successor (`+ω-iter n`, a `sucV`-chain) forces the conversion checker to normalize the whole chain against the level's union representation, and the cost is super-linear in the depth. State the witness at a SHALLOW index and climb by the limit-ordinal successor closure (`limit-succ-mem`, `L.Rud.Hierarchy:455`), one step per line....
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:955
- **C-42. A refutation measures the site it names, and it never measures how far that site extends**
  **Rule:** A refutation is a measurement of ONE site. It says the statement there is false. **It says nothing about how many other sites carry the same false shape.** So when a refutation lands, the next action is not the cure. **It is the sweep: search the tree for the shape, and report the COUNT before you price the cure.** A cure funded against the named site is priced against a number nobody...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:3725

## THE REASONING

`[LJ-1.384]` returned ESCAPE-OPEN against the sentence that every cheap escape
from the `sq` untruncation is closed. It named ONE candidate route that no leg
of the five covers: select the witness as a CODE, by leastness in the sealed
internal order, then read it out to ambient data. Legs 2 and 3 of that route sit
green in `src/` today. Leg 1 is unpriced.

**The recorded closure of this route is one INFERRED sentence and the tree
refutes it.** `[LJ-1.375]` section 3.4 closed the door by saying an internal
choice set would still need an external read-out, which is "the same
untruncation" (`agents/tasks/LJ-1-375/lj-1.375-report.md:346-349`). The read-out
of a CODED injection is not the same untruncation: a coded graph is
single-valued by its `svAt` conjunct, so its read-out is the unique-choice
shape, which `dev/literature/truncation-and-selection.md:92-95` records as the
one free case.

**No price is carried into this brief, and W3 is why.** The nearest recorded
figure, `[LJ-1.327]`'s ABOUT 820 lines, priced a DIFFERENT object: coding
`pairomega`'s well-founded recursion. This route does not code the pairing. It
needs internal EXISTENCE by whatever internal argument is cheapest, plus
leastness. `dev/LESSONS.md` P-l forbids transferring that figure, so the widest
unmeasured term IS leg 1 and this probe is its measurement.

**Do the cheapest decisive thing.** State the proposition at ONE band ordinal.
Try the delivered internal machinery, `orderAt`, `phi-less` and replacement. Do
not build a general theory of internal pairing.

## WHAT GO AND NO-GO EACH EARN

**A GO earns a second door out of the untruncation with no new axiom.** It would
mean the coded-witness route is live, that leg 1 is producible from delivered
machinery, and that the untruncation debt has a route nobody had aimed at. The
next task would then price the route whole, not this leg alone.

**A NO-GO earns the sentence that every cheap escape is closed**, which
`[LJ-1.384]` measured UNEARNED. A NO-GO must name the obstruction at
`file:line` and say what would have to change to move it. That converts
`[LJ-1.375]` section 3.4's INFERRED sentence into a measurement, which is worth
as much as a GO and costs less. **A stated NO-GO is a full return and not a
failure.**

## BRANCHES
```toml pod-branches
[[branch]]
id = "go"
priority = 10
action = "done"
outcome = "go"

  [branch.when]
  exit_code = 0
  obligations_delta_max = -2
  heap_wall = false

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  error_class = "unsolved_meta"
  changed_files_any = ["agents/tasks/LJ-1-386/review-of-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-386/Probe386.agda"]
  changed_files_none = ["agents/tasks/LJ-1-386/review-of-*.md"]

[[branch]]
id = "heap-wall-escalate"
priority = 30
action = "escalate"
head_slot = "mathematician_adversarial"

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

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev/TASKS-archived.md, archive/dev/JOURNAL-archived.md, archive/dev/DECISIONS-archived.md, dev/ARCHIVE.md:
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 253.381)
- CANDIDATE dev/ARCHIVE.md  (score 188.291)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 161.674)
- CANDIDATE archive/dev/TASKS-archived.md  (score 115.978)
- CANDIDATE archive/src/2026-08-09-rud-route/Everything.lagda.md  (score 71.918)

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 93.327)
- CANDIDATE dev/literature/devlin-II5.md  (score 68.021)
- CANDIDATE dev/literature/digest.md  (score 53.476)
- CANDIDATE dev/literature/terms-2026-08.md  (score 52.329)
- CANDIDATE dev/literature/geology.md  (score 41.124)
