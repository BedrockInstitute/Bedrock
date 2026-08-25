# LJ-1.394: the ambient descent, and what the negation of `AmbCard` delivers

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build TWO terms in `agents/tasks/LJ-1-394/Probe394.agda`, at a GENERIC ordinal.

    descent-amb : (α β : V ℓ) → IsOrd α → IsOrd β
                → ⟨ β ∈ α ⟩ → ⟨ ω ∈ β ⟩
                → (⟪ α ⟫ ↪ ⟪ β ⟫) → sq β → sq α

    not-ambcard-gives :
        (α : V ℓ) → IsOrd α → ⟨ ω ∈ α ⟩
      → (((β : V ℓ) → IsOrd β → ⟨ β ∈ α ⟩ → ⟨ ω ∈ β ⟩
                    → (⟪ α ⟫ ↪ ⟪ β ⟫) → Empty.⊥) → Empty.⊥)
      → Σ[ β ∈ V ℓ ] (IsOrd β × ⟨ β ∈ α ⟩ × ⟨ ω ∈ β ⟩ × (⟪ α ⟫ ↪ ⟪ β ⟫))

`descent-amb` is the cheap half and it is four arrows:

    ⟪ α ⟫ × ⟪ α ⟫  ↪  ⟪ β ⟫ × ⟪ β ⟫  ↪  ⟪ β ⟫  ↪  ⟪ α ⟫

The first is the given injection applied twice. The second is `sq β`. The third
is the inclusion of a member in an ordinal, which `[LJ-1.390]` already built as
`mem-incl` (`agents/tasks/LJ-1-390/Probe390.agda:76-89`). **Port those 12 lines
or re-derive them, and say in the report which you did.**

`not-ambcard-gives` is the hard half and it is the task's real question. **It
takes a NEGATION and it must return DATA.** `lem` decides the hypothesis,
because it is a function into `Empty.⊥` and so a proposition, but the
CONCLUSION is a `Σ` carrying a function, and that is not a proposition.

**`not-ambcard-gives` IS EXPECTED TO FAIL, AND A CLEAN FAILURE IS THE FULL
RETURN.** **If it fails, say exactly which step fails and what principle would
close it, at `file:line`, and stop.** Do not weaken the statement until it
passes. Do not add a postulate. Section WHAT GO AND NO-GO EACH EARN says why a
NO-GO is worth the dispatch.

**BUILD `descent-amb` FIRST.** It does not depend on the second term, and it is
the half that is certain to land.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-394/Probe394.agda::descent-amb",
               "agents/tasks/LJ-1-394/Probe394.agda::not-ambcard-gives"]

## SCOPE (write)
- agents/tasks/LJ-1-394/Probe394.agda
- agents/tasks/LJ-1-394/lj-1.394-report.md

## PREMISES
- `sq` is the ambient pairing, stated over `V ℓ`. Basis: src/L/Ordinal/SquareLaw.lagda.md:685-687
- `[LJ-1.390]` built `mem-incl`, the member-to-ordinal inclusion, in 12 lines and green. Basis: agents/tasks/LJ-1-390/Probe390.agda:76-89
- `[LJ-1.390]` built the same four-arrow composite with the descending arrow as a variable, and measured it. Basis: agents/tasks/LJ-1-390/Probe390.agda:110-131
- `[LJ-1.390]` measured that the same mathematics cost 175.42 s in one term and 1.54 s in two, and named the cure. Basis: agents/tasks/LJ-1-390/lj-1.390-report.md:172-179
- The cure was to take the descending arrow as a parameter and apply the door once outside. Basis: agents/tasks/LJ-1-390/Probe390.agda:135-142
- `lem` is the only classical principle this tree carries, and it is stated at `ℓ-suc ℓ`. Basis: src/L/StageCardinal.lagda.md:15
- `lowerLEM` moves that principle down one level, which is the tree's own way of spending it. Basis: src/L/CantorBernstein.lagda.md:7
- The one untruncation device this tree holds selects a LEAST CODE, and it works because `InjCode` is a proposition and `orderAt` well-orders the codes. Basis: agents/tasks/LJ-1-314/CodeUntrunc.agda:75-101
- The literature digest says a canonical injection needs a well-order on the INJECTIONS, which an ambient function type does not carry. Basis: dev/literature/truncation-and-selection.md:334-336
- `ord-tri` gives the ordinal trichotomy. Basis: src/L/Ordinal/Linear.lagda.md:136
- `mem-ord` gives the ordinal certificate at a member. Basis: src/L/Ordinal.lagda.md:221-222
- `∈-irrefl`. Basis: src/V/Hierarchy.lagda.md:155
- `fiber`, `member` and `↪-inj` are the three presentation lemmas every ambient injection in this tree is built from. Basis: src/V/Presentation.lagda.md:31-38
- `_↪_`, the injection type. Basis: src/L/Cardinal.lagda.md:47-48
- THE ARCHIVED ROUTE PRICED THIS DESCENT IN THE TRUNCATED GRADE AT ABOUT 18 LINES, and said its input was delivered and the descent itself was not built for budget. Basis: agents/tasks/archive/L3-32-T47/l3.32-t47-report.md:143-149
- The archived input was `Card.least`'s truncated equinumerosity witness, over an AMBIENT equivalence and not a code. Basis: archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:599-610
- The live tree's analogue selects over CODES and not over ambient equivalences, so the archived 18 does not transfer. Basis: src/L/Cardinal.lagda.md:235-258
- The archived route recorded that the honest UNTRUNCATED transfer stays blocked. Basis: agents/tasks/archive/L3-32-T47/l3.32-t47-report.md:155-158

## WHAT IS DELIVERED ALREADY
- `mem-incl`, green at a generic ordinal: agents/tasks/LJ-1-390/Probe390.agda:76-89
- `descent-core`, the same composite with a coded descending arrow: agents/tasks/LJ-1-390/Probe390.agda:110-131
- `sq`: src/L/Ordinal/SquareLaw.lagda.md:685-687
- `squareω`, the supply at `ω`: src/L/InjChain.lagda.md:184-185
- `lem`, and `lowerLEM` to move it down: src/L/StageCardinal.lagda.md:15, src/L/CantorBernstein.lagda.md:7
- `ord-tri`: src/L/Ordinal/Linear.lagda.md:136
- `mem-ord`: src/L/Ordinal.lagda.md:221-222
- `∈-irrefl`: src/V/Hierarchy.lagda.md:155
- `fiber`, `member`, `↪-inj`: src/V/Presentation.lagda.md:31-38
- A probe header that already opens most of these: agents/tasks/LJ-1-390/Probe390.agda:29-50

## WHAT IS MISSING

**`[LJ-1.393]` MOVES THE SQUARE LAW'S DEMAND FROM `Init` TO `AmbCard`. NOTHING
MEASURES WHAT THAT MOVE COSTS.** A recursion over the band ordinals must split
on whether the ordinal is an `AmbCard`. The positive side is `[LJ-1.393]`. **The
negative side is this task, and it is where the ambient route can die.**

**THE NEGATIVE SIDE IS NOT A PROPOSITION AND THAT IS THE WHOLE PROBLEM.** The
recursion needs `sq α`, which is a function with an injectivity proof. To reach
it from the failure of `AmbCard α` the proof must NAME a smaller ordinal and NAME
an injection into it. **A negation names nothing.**

**THE TREE HAS ONE DEVICE FOR EXACTLY THIS AND IT MAY NOT REACH.**
`code-untruncates` opens a truncation by selecting the LEAST CODE
(`agents/tasks/LJ-1-314/CodeUntrunc.agda:75-101`), and it works only because
`InjCode` is a proposition and the codes carry `orderAt`. **The ordinal `β` here
does carry an order. The injection does not.** So a selection might reach the
ordinal and still not reach the arrow. **Measure which of the two it reaches.**

**THE ARCHIVE PRICED THE TRUNCATED VERSION OF THIS DESCENT AND NEVER BUILT IT.**
`[L3.32-T47]` recorded it as「about 18 lines from `Card.least`'s witness
`∥ ⟪ β ⟫ ≃ ⟪ κ ⟫ ∥₁`, carrying `∥ sq κ ∥₁` to `∥ sq β ∥₁`」, not delivered for
budget, with its input delivered
(`agents/tasks/archive/L3-32-T47/l3.32-t47-report.md:143-149`). **THAT 18 DOES
NOT TRANSFER AND THE BOUNDARY SAYS SO.** The archived input was an AMBIENT
equinumerosity selected over `⟪ sucV α ⟫`
(`archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:599-610`); the
live tree's `InternalLeastCard` selects over CODES
(`src/L/Cardinal.lagda.md:235-258`). **Two different selections, two different
prices. Read the archived module, say what it gives, and re-measure at this
site.**

## THE REASONING

**`descent-amb` IS A RE-MEASUREMENT AND NOT A PORT, AND THE BOUNDARY SAYS SO.**
`[LJ-1.390]` built the same four-arrow composite with a CODED descending arrow
(`agents/tasks/LJ-1-390/Probe390.agda:110-131`) and measured 1.44 s. **That
number does not transfer.** This composite replaces the coded arrow and the door
by one ambient arrow, so it is a different term at a different site.

**THE COST LESSON FROM `[LJ-1.390]` DOES TRANSFER AS A WARNING AND NOT AS A
NUMBER.** The same mathematics cost 175.42 s in one term and 1.54 s in two
(`agents/tasks/LJ-1-390/lj-1.390-report.md:172-179`), and the cure was to take
the descending arrow as a parameter. **Take it as a parameter here too**, and if
the cost appears anyway, report it as a WALL event and never simply rerun.

**FOR `not-ambcard-gives`, TRY THE TWO STEPS SEPARATELY AND REPORT BOTH.**

1. **Does `lem` reach the ORDINAL?** Can you produce, from the negation, a
   `β` with `IsOrd β`, `β ∈ α` and `ω ∈ β`, even merely? The ordinals below `α`
   carry an order, so a least-of selection may apply.
2. **Does anything reach the ARROW?** Given that `β`, can you produce the
   injection `⟪ α ⟫ ↪ ⟪ β ⟫` as data?

**A report that answers step 1 YES and step 2 NO is the most useful outcome this
task can have**, because it says exactly where the ambient route needs a code
and how little of it needs one.

**DO NOT CHANGE THE STATEMENT TO MAKE IT PASS.** A `not-ambcard-gives` that
returns a truncation is a different theorem and it does not serve the recursion.
If you believe the truncated form is what the campaign should want, say so in
the report as a RECOMMENDATION and leave the stated obligation failed. That
judgement belongs to the mathematician and not to this task.

**W2 AND DD4.** Both terms are generic in the ordinal. Nothing here may name a
site.

**W3, THE WIDEST UNMEASURED TERM AND ITS PROBE.** The widest unmeasured term is
step 2 above: **whether this tree can select an ambient injection from a merely
existing family.** **The probe is `not-ambcard-gives` itself, split into its two
steps.** **The estimate is about 20 code lines for `descent-amb`, on the basis of
a delivered comparable of SHAPE: `descent-core` is 18 code lines for the same
four arrows** (`agents/tasks/LJ-1-390/Probe390.agda:110-131`). **`not-ambcard-gives`
is UNPRICED and this brief gives it no number**, because the one comparable in
the tree, `code-untruncates`, works by a property that its subject does not have.

**WRITE THE REPORT FIRST AND FILL IT AS YOU GO** (C-22). Run the probe while
this task is live. Nothing typechecks it after the task closes.

**REPORT THE NUMBER YOU MEASURED.** Give the wall seconds at the caliber the
program set on your pane, as the median of three consecutive runs, and give the
empty-module floor on the same machine on the same day.

## WHAT GO AND NO-GO EACH EARN

**A GO on both terms closes the ambient route's case split** and leaves
`[LJ-1.395]` a recursion with every case supplied. That would be the largest
single step this campaign has taken toward the square law.

**A NO-GO on `not-ambcard-gives` earns the exact boundary between what the
ambient grade can do and what it cannot.** It would say the recursion must carry
codes at its case split and nowhere else, which prices the coded machinery
against ONE step instead of against the whole route. **That is a smaller and
better-understood bill than the campaign holds today. A stated NO-GO is a full
return and not a failure.**

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
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-394/Probe394.agda"]
  changed_files_none = ["agents/tasks/LJ-1-394/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  error_class = "unsolved_meta"
  changed_files_any = ["agents/tasks/LJ-1-394/review-of-*.md"]

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

## LAWS (program-generated, do not edit)

MANDATORY for kind `probe` (measures one thing and keeps the file as the report's other half. Gating, heap discipline, the transplant law, which is what a probe most often gets wrong, and the extent law, because a probe that refutes has measured ONE site.):

- **D-1. The probe doctrine**
  **Rule:** Before committing to a heavy or hard-to-reverse path, run the cheapest decisive probe with its abort criterion fixed in advance; a red verdict costs the attempt and nothing else.
  Full entry: dev/LESSONS.md:1064
- **P-l. A statement may be ABOUT a concrete stage without dragging that stage's PRESENTATION into its type**
  **The law.** Being about a concrete position is not what costs. Naming a transparent construction in a statement's TYPE is. If the tower's stage values are `opaque` upstream, a theorem may quantify over, hypothesize about and conclude at `Sset ω` freely, because the stage is an ATOM to the elaborator and nothing unfolds. If instead the type mentions a transparent presentation, such as `⟪ sucV (...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2357
- **P-i. The conversion-explosion playbook (imported from the source project)**
  **Rule:** When cubical Agda hangs or exhausts memory on this codebase family, the cause is one of three heavy-thing classes forced into normalization, and the cure is selected by the decision tree below, not by trial. Imported whole from the antecedent development's worklog (`../fol-reification/docs/WORKLOG.md` §5, twenty measured cases); read that section before any surgery on a hang.
  Full entry: dev/LESSONS.md:229
- **C-12. Agda runs under a hard heap cap; parallel writers under a quota**
  **Rule:** Every agda invocation runs under a GHC heap cap (`GHCRTS=-M<n>g`) so a runaway typecheck dies with a clean "Heap exhausted" exit instead of OOM-killing the machine; the orchestrator's audits run at `-M16g` and `make` exports a default. Sub-agent concurrency is TIERED (owner-widened 2026-08-02 once the caps and the watchdog were live): WIDE mode for routine batches, up to FOUR concurre...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2135
- **D-10. Price the truth of a recorded residue before pricing its proof**
  **Rule:** A residue recorded under the wall protocol names a TARGET, and a target can be false; before dispatching a discharge batch, spend the five minutes checking the target's truth at the intended generality (a Tarskian or cardinality obstruction is the usual killer), and record the corrected target beside the original.
  Full entry: dev/LESSONS.md:1375
- **C-22. A dispatched agent writes its deliverable incrementally, never at the end**
  **Rule:** When an agent's deliverable is a file, the brief must require it WRITTEN EARLY as a skeleton and filled incrementally, saving after each answer lands. An agent that researches for its whole budget and leaves the writing to the end returns nothing when the budget runs out, and its research dies with it. A partial dossier is a real deliverable; an unwritten perfect one is not.
  Full entry: dev/LESSONS.md:2297
- **R-40. A deep successor-chain membership witness normalizes super-linearly; climb by small closures**
  **Rule:** An ordinal-membership premise stated at a deep iterated successor (`+ω-iter n`, a `sucV`-chain) forces the conversion checker to normalize the whole chain against the level's union representation, and the cost is super-linear in the depth. State the witness at a SHALLOW index and climb by the limit-ordinal successor closure (`limit-succ-mem`, `L.Rud.Hierarchy:455`), one step per line....
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:955
- **C-42. A refutation measures the site it names, and it never measures how far that site extends**
  **Rule:** A refutation is a measurement of ONE site. It says the statement there is false. **It says nothing about how many other sites carry the same false shape.** So when a refutation lands, the next action is not the cure. **It is the sweep: search the tree for the shape, and report the COUNT before you price the cure.** A cure funded against the named site is priced against a number nobody...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:3752

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev/TASKS-archived.md, archive/dev/JOURNAL-archived.md, archive/dev/DECISIONS-archived.md, dev/ARCHIVE.md:
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 174.218)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 154.121)
- CANDIDATE dev/ARCHIVE.md  (score 148.566)
- CANDIDATE archive/dev/TASKS-archived.md  (score 103.886)
- CANDIDATE archive/src/2026-08-09-rud-route/L/Condensation.lagda.md  (score 48.603)

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 56.229)
- CANDIDATE dev/literature/devlin-II5.md  (score 49.425)
- CANDIDATE dev/literature/digest.md  (score 40.593)
- CANDIDATE dev/literature/geology.md  (score 31.536)
- CANDIDATE dev/literature/devlin-errata.md  (score 27.019)
