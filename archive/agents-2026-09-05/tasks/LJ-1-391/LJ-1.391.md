# LJ-1.391: can `sq` be TRUNCATED? The collection step, measured

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build TWO terms in `agents/tasks/LJ-1-391/Probe391.agda`. `sq` is
`src/L/Ordinal/SquareLaw.lagda.md:685-687` and it is stated over `V ℓ`.

    sq-collect : ((δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
                            → ∥ sq δ ∥₁)
               → ∥ ((δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
                              → sq δ) ∥₁

    sq-collect-suffices :
        ((δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → sq δ)
      → (α : V ℓ) → IsOrd α → ⟨ α ∈ sucV α₀ ⟩ → (⟨ α ∈ ω ⟩ → Empty.⊥)
      → ∥ ⟪ Lset α ⟫ ↪ ⟪ α ⟫ ∥₁

`sq-collect` moves a POINTWISE mere square law to a MERE WHOLE square law. It is
the risk and it is why this task exists.

`sq-collect-suffices` is the payoff and it is cheap: instantiate
`L.StageCardinal` with the collected family and apply `Upper.stage-card-upper`,
then `∣_∣₁`. It shows the collected form is ENOUGH for the one consumer.

**TAKE `α₀` AND `oα₀` AS PARAMETERS OF YOUR OWN PROBE MODULE.** Do not name an
ordinal. Nothing below may name `ω · 2`, `+ω` or any other site.

**`sq-collect` IS THE AXIOM OF CHOICE AND THE DIGEST SAYS SO. DO NOT PRESENT IT
AS A NEW STATEMENT.** `dev/literature/truncation-and-selection.md:223-235` gives
the HoTT Book's form `(∏x ∥Y x∥) → ∥∏x Y x∥` and names it 3.8.1. That is
`sq-collect`, at the index type of the band ordinals. **So this task is not
asking you to invent a principle. It is asking what this tree can prove without
one, and what it would cost to assume one.**

**`sq-collect` IS EXPECTED TO FAIL, AND A CLEAN FAILURE IS THE FULL RETURN.**
The tree carries `lem : LEM (ℓ-suc ℓ)` and no choice, and LEM does not give
choice. **If it fails, say so, name the principle as the digest names it, and
stop.** Do not weaken the statement until it passes. Do not add a postulate. A
NO-GO here is worth more than a GO, and section WHAT GO AND NO-GO EACH EARN says
why.

**THE DIGEST ALSO SUPPLIES THE HALF THAT DOES WORK, AND IT IS WHY THE SECOND
TERM MATTERS.** Section 2.7 says AC delivers `∥ f ∥₁` and never `f`, so **if the
goal that consumes `f` is not a proposition, AC does not help**
(`dev/literature/truncation-and-selection.md:229-232`). `sq-collect-suffices`
concludes inside `∥_∥₁`, which IS a proposition, so the pair composes. **Check
that reading and say so.**

**BUILD `sq-collect-suffices` FIRST.** It does not depend on `sq-collect`, and
it is the half that is certain to land. Then attempt `sq-collect`.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-391/Probe391.agda::sq-collect",
               "agents/tasks/LJ-1-391/Probe391.agda::sq-collect-suffices"]

## SCOPE (write)
- agents/tasks/LJ-1-391/Probe391.agda
- agents/tasks/LJ-1-391/lj-1.391-report.md

## PREMISES
- `sq` enters the tree ONLY as a module parameter of `L.StageCardinal`, quantified over every `δ` with `δ ∈ sucV α₀` and `δ ∉ ω`. Basis: src/L/StageCardinal.lagda.md:17-20
- That parameter is applied at exactly ONE place inside the chapter. Basis: src/L/StageCardinal.lagda.md:283
- The chapter's own conclusion is UNTRUNCATED data, and its recursion motive `P` is an untruncated `Σ`. Basis: src/L/StageCardinal.lagda.md:530-533
- The recursion is `∈-induction` over that motive. Basis: src/L/StageCardinal.lagda.md:564-566
- The second application site is `L.BoundedSubset`, which instantiates the same chapter. Basis: src/L/BoundedSubset.lagda.md:1410
- The GCH trophy states its injections MERELY: `InjL` is a propositional truncation. Basis: src/L/GCH.lagda.md:37-38
- The trophy's whole conclusion is a truncated existential. Basis: src/L/GCH.lagda.md:59-66
- A truncated square law is already delivered under `Init`, so the truncated grade is not a new object in this tree. Basis: src/L/Ordinal/SquareLaw.lagda.md:963-964
- `∈-induction` is delivered and needs no new well-foundedness. Basis: src/V/Hierarchy.lagda.md:177-180
- The one untruncation device this tree holds selects a LEAST CODE, and it works because `InjCode` is a proposition and `orderAt` well-orders the codes. Basis: agents/tasks/LJ-1-314/CodeUntrunc.agda:75-101
- The literature digest predicts that an ambient function type carries no well-order on the injections, which is what a selection needs. Basis: dev/literature/truncation-and-selection.md:334-336
- `_↪_`, the injection type both grades speak in. Basis: src/L/Cardinal.lagda.md:47-48
- THE ARCHIVED ROUTE ASKED THIS QUESTION AND ANSWERED IT FOR ITS OWN CONSUMERS: every conclusion-side consumer of the counting is proposition-valued, so the truncated form sufficed there. Basis: agents/tasks/archive/L3-32-T47/l3.32-t47-report.md:155-158
- The archived route DELIVERED the truncated square law at every initial ordinal. Basis: agents/tasks/archive/L3-32-T47/l3.32-t47-report.md:39
- The archived `[T43]` recorded the same finding first, and its reason was that every elimination of the induction hypothesis lands in the empty type. Basis: archive/dev/JOURNAL-archived.md:1623-1631
- AND THE ARCHIVED `[T46]` MEASURED THE COUNTEREXAMPLE THE SAME HOUR: one call site's goal is NOT proposition-valued, because its first component is a function. Basis: archive/dev/JOURNAL-archived.md:1696-1699
- The archived route recorded that the honest untruncated transfer stays BLOCKED. Basis: agents/tasks/archive/L3-32-T47/l3.32-t47-report.md:155-156
- THE DIGEST NAMES `sq-collect` AS THE HoTT BOOK'S AXIOM OF CHOICE, whose conclusion is already truncated. Basis: dev/literature/truncation-and-selection.md:223-235
- The digest says AC delivers a merely-existing selection and never a selection, so it helps only when the consuming goal is a proposition. Basis: dev/literature/truncation-and-selection.md:229-232
- The digest says a cardinal inequality IS a truncated existence of an injection, by the HoTT Book's own definition, and that a formalization stating its conclusion with the injection as DATA asks for what the sources do not supply. Basis: dev/literature/truncation-and-selection.md:72-86
- The digest lists「must a trophy statement carry data rather than a truncation」as an OWNER'S RULING that this project has not made, and names section 1.5 as the evidence. Basis: dev/literature/truncation-and-selection.md:338-340

## WHAT IS DELIVERED ALREADY
- The consumer and its `sq` parameter: src/L/StageCardinal.lagda.md:15-20
- `Upper.stage-card-upper`, the untruncated conclusion: src/L/StageCardinal.lagda.md:564-566
- `sq` and `Init`: src/L/Ordinal/SquareLaw.lagda.md:685-700
- `via-col-truncated`, the truncated supply under `Init`: src/L/Ordinal/SquareLaw.lagda.md:963-964
- `squareω`, the untruncated supply at `ω`: src/L/InjChain.lagda.md:184-185
- `∈-induction`: src/V/Hierarchy.lagda.md:177-180
- A probe header that already opens `L.StageCardinal`'s neighbours: agents/tasks/LJ-1-390/Probe390.agda:29-50
- **THE ARCHIVED ANSWER TO THIS EXACT QUESTION, on the retired route**: agents/tasks/archive/L3-32-T47/l3.32-t47-report.md:3-26 and :135-158
- The archived tension, recorded before it was resolved: archive/dev/JOURNAL-archived.md:1690-1704

## WHAT IS MISSING

**NOBODY HAS ASKED WHETHER THE SQUARE LAW MUST BE DATA.** Every dispatch since
`[LJ-1.384]` has assumed it must. `[LJ-1.386]` built the coded-witness door to
untruncate (`agents/tasks/LJ-1-386/Probe386.agda:264-268`). `[LJ-1.390]` priced
a descent whose whole risk is that `Init` has no producer
(`agents/tasks/LJ-1-390/lj-1.390-report.md:20-27`). Both prices are paid for
UNTRUNCATED `sq`.

**AND THE TROPHY ITSELF IS TRUNCATED.** `InjL` is a propositional truncation
(`src/L/GCH.lagda.md:37-38`) and `GCHStatement` concludes inside `∥_∥₁`
(`src/L/GCH.lagda.md:59-66`). So the endpoint speaks in the merely-grade, and
whether the middle of the chain must speak in the data-grade is an open
question that nobody has measured.

**THIS TASK MEASURES IT, AND IT MEASURES THE ONE STEP THAT DECIDES IT.** The
consumer spends `sq` at one place (`src/L/StageCardinal.lagda.md:283`), so a
single `PT.rec` at the module boundary would carry a mere `sq` through, IF the
whole family can be collected under one truncation first. **The collection is
the step. Everything else is bookkeeping.**

**THE ARCHIVE ASKED THIS QUESTION IN AUGUST AND ITS ANSWER WAS YES, FOR A
DIFFERENT CHAPTER.** `[L3.32-T43]` found that every conclusion-side consumer of
the archived counting is proposition-valued, so the truncated form suffices
there, and its reason was that every elimination of the induction hypothesis
lands in the empty type (`archive/dev/JOURNAL-archived.md:1623-1631`).
`[L3.32-T47]` then built the truncated layer and delivered
`initial-square-law : (α : S) → Init α → ∥ sq α ∥₁`
(`agents/tasks/archive/L3-32-T47/l3.32-t47-report.md:39`), and recorded that the
honest untruncated transfer stays BLOCKED (`:155-158`).

**AND `[L3.32-T46]` MEASURED THE COUNTEREXAMPLE THE SAME HOUR.** One call site's
goal is NOT proposition-valued, because its first component is a function, so a
truncated equinumerosity cannot supply it as the goal stands
(`archive/dev/JOURNAL-archived.md:1696-1699`). **The two findings were recorded
as a live tension and the archive says so in those words.**

**SO WHAT IS MISSING IS NOT THE IDEA. IT IS THE MEASUREMENT AT THE LIVE
CHAPTER.** `src/L/StageCardinal.lagda.md` was written on the internalization
route and not on the archived one, and it demands the UNTRUNCATED form
(`:17-20`, `:530-533`, `:564-566`). **Whether it is a `[T43]` site or a `[T46]`
site is what nobody has measured, and it is this task.**

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

## THE REASONING

**THE CAMPAIGN IS ABOUT TO FUND TWO EXPENSIVE ROUTES AND BOTH ARE PAID FOR ONE
ASSUMPTION.** The product route owes a coded injection out of an internal square
at every band ordinal (`agents/tasks/LJ-1-388/lj-1.388-report.md:236-248`). The
descent route owes `Init` at every internal cardinal, and `Init` has no producer
in the tree (`agents/tasks/LJ-1-390/lj-1.390-report.md:20-27`). **Both prices
buy the same thing: an UNTRUNCATED pairing function.** This task asks whether
the campaign must buy it.

**THE ONE STEP THAT DECIDES IT.** The consumer applies `sq` once
(`src/L/StageCardinal.lagda.md:283`), so one `PT.rec` at the module boundary
carries a mere `sq` through the whole chapter. `PT.rec` needs the family under
ONE truncation, and what you hold is one truncation per ordinal. **That gap is
`sq-collect` and it is the whole task.**

**WHY IT IS EXPECTED TO FAIL, AND WHY YOU MUST STILL TRY IT.** The statement is
a choice principle over the ordinals below `sucV α₀`. The tree carries
`lem : LEM (ℓ-suc ℓ)` and nothing else of that kind. LEM does not give choice.
**But the tree DOES carry a selection device**: `leastOf` over `orderAt` picks a
least CODE (`agents/tasks/LJ-1-314/CodeUntrunc.agda:75-101`), and the campaign
uses it exactly where a truncation must open. **So the honest question is not
"does choice hold" but "does this tree's selection device reach an ambient
pairing function".** Answer that, at `file:line`.

**THE DIGEST ALREADY PREDICTS THE ANSWER AND THAT IS NOT A REASON TO SKIP THE
MEASUREMENT.** `dev/literature/truncation-and-selection.md:334-336` says a
canonical injection needs a well-order on the INJECTIONS, which `<_L` supplies
classically and an ambient function type does not. **Read that line. Then
measure whether it applies here**, because a prediction is not a `file:line` in
this tree.

**READ THE ARCHIVE FIRST AND SAY WHAT YOU TOOK.** `[L3.32-T43]`, `[L3.32-T46]`
and `[L3.32-T47]` fought this exact question on the retired route and left three
records: the finding, the counterexample and the delivered truncated layer
(`archive/dev/JOURNAL-archived.md:1623-1631`, `:1696-1699`, and
`agents/tasks/archive/L3-32-T47/l3.32-t47-report.md:3-26`). **`[T43]`'s reason
is the one to test at the live chapter**: every elimination of the induction
hypothesis lands in the empty type. `L.StageCardinal`'s recursion eliminates its
own hypothesis in `branch` (`src/L/StageCardinal.lagda.md:534-560`), and that
elimination does NOT land in the empty type: it lands in an injection. **Check
that reading. If it is right, this chapter is a `[T46]` site and `sq-collect` is
not the only thing that fails.**

**`[T43]` ALSO PRICED AND REJECTED A CHOICE PRINCIPLE, AND ITS REASON HAS
MOVED.** The journal records that a choice principle implies excluded middle and
would cost the tree's postulate-free claim
(`archive/dev/JOURNAL-archived.md:1630`). **This tree now carries `lem` as a
module parameter** (`src/L/StageCardinal.lagda.md:15`), so that objection is not
what it was in August. **Say in the report whether a choice principle stated the
same way would now be admissible, and do not decide it**: that is the owner's
call and not this task's.

**DO NOT RE-PROVE THE CHAPTER.** `sq-collect-suffices` instantiates
`L.StageCardinal` and applies `Upper.stage-card-upper`
(`src/L/StageCardinal.lagda.md:564-566`). It re-proves nothing. If you find
yourself rebuilding `LimitStep`, stop and say so: that is a different task and it
is not this one.

**W2 AND DD4.** Both terms are generic in `α₀` and in `δ`. A collection stated
at one ordinal measures one ordinal and settles nothing.

**W3, THE WIDEST UNMEASURED TERM AND ITS PROBE.** The widest unmeasured term is
`sq-collect` itself, and this task IS its probe. **The estimate is about 35 code
lines for the two terms together, and the basis is a comparable of SHAPE and not
of size**: `descent-closes` with its motive and its step is 29 code lines for the
same kind of shell (`agents/tasks/LJ-1-390/Probe390.agda:180-219`). **Do not
fund anything against 35.** A `sq-collect` that fails costs almost no lines and
returns the whole value of this task.

**WRITE THE REPORT FIRST AND FILL IT AS YOU GO** (C-22). Run the probe while
this task is live. Nothing typechecks it after the task closes.

**REPORT THE NUMBER YOU MEASURED.** Give the wall seconds at the caliber the
program set on your pane, as the median of three consecutive runs, and give the
empty-module floor on the same machine on the same day.

## WHAT GO AND NO-GO EACH EARN

**A GO RETIRES THE DOOR, THE INTERNAL PRODUCT AND THE `Init` PRODUCER FROM THE
CRITICAL PATH.** It would mean the campaign needs only `∥ sq δ ∥₁` pointwise,
which `via-col-truncated` already supplies under `Init`
(`src/L/Ordinal/SquareLaw.lagda.md:963-964`) and which a truncated recursion can
carry. That is the largest saving available to this campaign today.

**A NO-GO PROVES THE DOOR IS LOAD-BEARING**, which nothing has yet established.
It would say the untruncated grade is forced, that `[LJ-1.386]`'s door is on the
critical path and not beside it, and that the campaign must buy a coded pairing.
**Name the principle the collection needs and the `file:line` where this tree
falls short of it.** A stated NO-GO is a full return and not a failure.

**EITHER WAY, THIS TASK FEEDS AN OWNER'S RULING AND DOES NOT MAKE IT.** The
digest lists「must a trophy statement carry data rather than a truncation」among
the questions it does not settle, and says the answer is the owner's
(`dev/literature/truncation-and-selection.md:338-340`). **Your report is the
measurement that ruling needs at the live chapter. Do not write the ruling.**

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
  changed_files_any = ["agents/tasks/LJ-1-391/Probe391.agda"]
  changed_files_none = ["agents/tasks/LJ-1-391/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  error_class = "unsolved_meta"
  changed_files_any = ["agents/tasks/LJ-1-391/review-of-*.md"]

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
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 198.554)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 169.198)
- CANDIDATE dev/ARCHIVE.md  (score 159.594)
- CANDIDATE archive/dev/TASKS-archived.md  (score 116.995)
- CANDIDATE archive/src/2026-08-09-rud-route/Everything.lagda.md  (score 62.532)

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 76.896)
- CANDIDATE dev/literature/devlin-II5.md  (score 57.609)
- CANDIDATE dev/literature/digest.md  (score 54.094)
- CANDIDATE dev/literature/terms-2026-08.md  (score 44.155)
- CANDIDATE dev/literature/geology.md  (score 41.738)
