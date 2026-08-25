# LJ-1.393: the ambient cardinal, and the first `Init` above omega

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build TWO terms in `agents/tasks/LJ-1-393/Probe393.agda`, at a GENERIC ordinal.

    AmbCard : V ℓ → Type (ℓ-suc ℓ)
    AmbCard α = (β : V ℓ) → IsOrd β → ⟨ β ∈ α ⟩ → ⟨ ω ∈ β ⟩
                          → (⟪ α ⟫ ↪ ⟪ β ⟫) → Empty.⊥

    amb-noinj² : (α : V ℓ) → IsOrd α → AmbCard α
               → ((β : V ℓ) → IsOrd β → ⟨ β ∈ α ⟩ → ⟨ ω ∈ β ⟩ → sq β)
               → (β : V ℓ) → IsOrd β → ⟨ β ∈ α ⟩ → ⟨ ω ∈ β ⟩
               → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
               → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥

    amb-init : (α : V ℓ) → IsOrd α → ⟨ ω ∈ α ⟩ → AmbCard α
             → ((β : V ℓ) → IsOrd β → ⟨ β ∈ α ⟩ → ⟨ ω ∈ β ⟩ → sq β)
             → Init α

`AmbCard` is a definition you write. It is the AMBIENT cardinality notion: no
ambient injection of `⟪ α ⟫` into a smaller infinite ordinal.

**ONE CLAUSE BINDS `AmbCard` AND IT EXISTS TO STOP ONE GAME.** `AmbCard` is
stated at `⟪ β ⟫` and NEVER at `⟪ β ⟫ × ⟪ β ⟫`. **A square-form definition makes
`amb-noinj²` the identity function and this whole task vacuous**, and the
archived route already took that shortcut for its own reasons:
`[L3.32-T47]` strengthened the exclusion hypothesis to its square form so that
the law-at-members hypothesis disappeared
(`agents/tasks/archive/L3-32-T47/l3.32-t47-report.md:14-19`). **THIS CAMPAIGN
MUST NOT**, because `[LJ-1.394]`'s descent consumes the non-square form: an
injection into a square descends nowhere without the square law you are trying
to prove. **If you believe the square form is right, say so in the report as a
RECOMMENDATION and leave the stated obligation as written.** That judgement is
the mathematician's.

`amb-noinj²` is `Init`'s FOURTH conjunct
(`src/L/Ordinal/SquareLaw.lagda.md:696-698`). It is one composition:
`f` maps into `⟪ β ⟫ × ⟪ β ⟫`, the second hypothesis pairs that down to `⟪ β ⟫`,
and `AmbCard α` refutes the result.

`amb-init` assembles all four conjuncts and is the deliverable.

**THE SECOND HYPOTHESIS IS THE INDUCTION HYPOTHESIS OF A RECURSION THIS TASK DOES
NOT WRITE.** It is `sq` at the infinite ordinal members of `α`. Take it as a
hypothesis. `[LJ-1.395]` supplies it. **Do not build a recursion here.**

**THE THIRD CONJUNCT COMES FROM `[LJ-1.392]`.** Take `amb-limit` as a hypothesis
of your module with the type `[LJ-1.392]` reports, and say in the report which
form you took. **If `[LJ-1.392]` returned NO-GO, take the clause as a bare
hypothesis and say so.** This task is not blocked by that.

**If `amb-init` cannot be built, state the obstruction at `file:line` and stop.
Both answers discharge this task.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-393/Probe393.agda::amb-noinj²",
               "agents/tasks/LJ-1-393/Probe393.agda::amb-init"]

## SCOPE (write)
- agents/tasks/LJ-1-393/Probe393.agda
- agents/tasks/LJ-1-393/lj-1.393-report.md

## PREMISES
- `Init` is four conjuncts and the fourth forbids an AMBIENT injection of the index into an infinite member's square. Basis: src/L/Ordinal/SquareLaw.lagda.md:692-700
- `InitialCore` takes that conjunct as a module PARAMETER, so the chapter consumes it and never produces it. Basis: src/L/Ordinal/SquareLaw.lagda.md:703-709
- `via-col-square` turns `Init α` into `sq α`, so an `Init` producer is a square law producer. Basis: src/L/Ordinal/SquareLaw.lagda.md:960-961
- The ONE delivered instance of the three hypotheses is at `ω`, and its fourth-conjunct analogue is vacuous there. Basis: src/L/InjChain.lagda.md:123-126
- `IsCardinalL`, the tree's OTHER cardinality notion, forbids a CODED injection and not an ambient one. Basis: src/L/Cardinal.lagda.md:230-233
- The tree's one bridge between the two grades runs CODED to AMBIENT, and nothing runs the other way. Basis: src/L/CantorBernstein.lagda.md:33-38
- The truncated form of that bridge is also coded to ambient. Basis: agents/tasks/LJ-1-386/Probe386.agda:264-268
- `[LJ-1.390]` measured that the descent route needs `Init` at an internal cardinal and that `Init` has no producer in the tree. Basis: agents/tasks/LJ-1-390/lj-1.390-report.md:20-27
- `sq` is the ambient pairing, stated over `V ℓ`. Basis: src/L/Ordinal/SquareLaw.lagda.md:685-687
- `ord-tri` gives the ordinal trichotomy. Basis: src/L/Ordinal/Linear.lagda.md:136
- `∈-irrefl`. Basis: src/V/Hierarchy.lagda.md:155
- `mem-ord` gives the ordinal certificate at a member. Basis: src/L/Ordinal.lagda.md:221-222
- `_↪_`, the injection type. Basis: src/L/Cardinal.lagda.md:47-48
- `FiniteBase.finite-excl` is the fourth argument `Initial` passes to `InitialCore`, and it is supplied from the second conjunct alone. Basis: src/L/Ordinal/SquareLaw.lagda.md:938-941
- THE SQUARE FORM OF THE EXCLUSION CLAUSE WAS A DELIBERATE ARCHIVED DESIGN DECISION, taken so that the law-at-members hypothesis disappeared. Basis: agents/tasks/archive/L3-32-T47/l3.32-t47-report.md:14-19
- The archived route delivered `Init`'s bound at every initial ordinal and left the three clauses to the consumer to verify. Basis: agents/tasks/archive/L3-32-T47/l3.32-t47-report.md:135-142

## WHAT IS DELIVERED ALREADY
- `Init`, `InitialCore`, `Initial`, `via-col-square`: src/L/Ordinal/SquareLaw.lagda.md:692-964
- `FiniteBase.finite-excl`, which `Initial` already supplies from `ω ∈ˢ α`: src/L/Ordinal/SquareLaw.lagda.md:938-941
- `Coreω` and the four clauses at `ω`: src/L/InjChain.lagda.md:109-171
- `IsCardinalL`, the coded notion this one is NOT: src/L/Cardinal.lagda.md:230-233
- `ord-tri`: src/L/Ordinal/Linear.lagda.md:136
- `mem-ord`: src/L/Ordinal.lagda.md:221-222
- `∈-irrefl`: src/V/Hierarchy.lagda.md:155
- `fiber`, `member`, `↪-inj`: src/V/Presentation.lagda.md:31-38
- `[LJ-1.392]`'s `amb-limit`, if it landed: agents/tasks/LJ-1-392/LJ-1.392.md:12
- A probe header that already opens most of these: agents/tasks/LJ-1-390/Probe390.agda:29-50

## WHAT IS MISSING

**THE TREE HAS TWO CARDINALITY NOTIONS AND THEY POINT OPPOSITE WAYS.** `Init`
forbids an AMBIENT injection (`src/L/Ordinal/SquareLaw.lagda.md:696-698`).
`IsCardinalL` forbids a CODED one (`src/L/Cardinal.lagda.md:230-233`). The one
bridge the tree holds runs coded to ambient
(`src/L/CantorBernstein.lagda.md:33-38`, and its truncated form at
`agents/tasks/LJ-1-386/Probe386.agda:264-268`). **Nothing runs ambient to
coded.**

**SO `IsCardinalL α → Init α` IS THE WRONG THING TO ASK FOR**, and `[LJ-1.390]`
named it as the descent route's whole risk
(`agents/tasks/LJ-1-390/lj-1.390-report.md:20-27`). It asks the bridge to run
the direction the tree does not have.

**THIS TASK ASKS A DIFFERENT QUESTION.** It does not bridge the two notions. It
introduces the AMBIENT notion directly and asks what `Init` costs from it. **The
answer is expected to be one composition**, because `Init`'s fourth conjunct and
`AmbCard` speak the same grade, and the only difference between them is a square
that the induction hypothesis flattens.

**WHAT THIS TASK DOES NOT SETTLE, AND THE REPORT MUST SAY SO.** It does not say
that `AmbCard` has a producer. It moves the demand from `Init` to `AmbCard`, and
`[LJ-1.394]` is where the campaign learns what that move costs. **A report that
presents `amb-init` as closing the square law is wrong.**

## THE REASONING

**BUILD `amb-noinj²` FIRST AND ALONE.** It is one composition and it is the
whole mathematical content of this task. If it does not go through, nothing else
here matters and you should stop and say why.

**THE COMPOSITION, IN ONE LINE.** Given `f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫` injective and
`sq β = Σ[ p ∈ (⟪ β ⟫ × ⟪ β ⟫ → ⟪ β ⟫) ] (injective)`, the composite
`fst (sq β) ∘ f` is an injection `⟪ α ⟫ ↪ ⟪ β ⟫`, and `AmbCard α β ...` refutes
it. **Watch the levels.** `sq` lands in `Type ℓ` and `Init` lands in
`Type (ℓ-suc ℓ)`, so a lift may be needed and it may be free.

**THE THIRD AND FOURTH ARGUMENTS `Initial` PASSES ARE NOT BOTH YOURS.**
`Initial` builds `finite-excl` itself from the second conjunct
(`src/L/Ordinal/SquareLaw.lagda.md:938-941`), so `amb-init` owes the first three
conjuncts of `Init` plus `amb-noinj²`, and NOT a finite-exclusion clause. **Read
those four lines before you write anything, because a clause built twice is a
clause priced twice.**

**DO NOT USE `IsCardinalL` ANYWHERE IN THIS TASK.** It is the coded notion and it
is not what this route runs on. If you find yourself importing `L.Cardinal` for
anything except `_↪_`, stop and ask whether the shape of this task is right.

**W2 AND DD4.** Everything is generic in the ordinal. `AmbCard` takes `α` and
names no site.

**W3, THE WIDEST UNMEASURED TERM AND ITS PROBE.** The widest unmeasured term is
**whether `AmbCard` is inhabited at any ordinal above `ω` in this tree**, and
this task does NOT measure it: this task measures only what `Init` costs GIVEN
it. Say that in the report in one line. **The probe that would measure it is
`[LJ-1.394]`'s second term**, which asks what the negation of `AmbCard`
delivers. **The estimate for THIS task is about 45 code lines for the three
items together, and the basis is a delivered comparable of SHAPE**: `Coreω`
supplies the same three `InitialCore` hypotheses at `ω`
(`src/L/InjChain.lagda.md:109-171`). **It is not a comparable of size**, because
two of its three clauses are vacuous at `ω` and none of them is vacuous here.
**Do not fund anything against 45.**

**WRITE THE REPORT FIRST AND FILL IT AS YOU GO** (C-22). Run the probe while
this task is live. Nothing typechecks it after the task closes.

**REPORT THE NUMBER YOU MEASURED.** Give the wall seconds at the caliber the
program set on your pane, as the median of three consecutive runs, and give the
empty-module floor on the same machine on the same day.

## WHAT GO AND NO-GO EACH EARN

**A GO earns the first producer of `Init` this repository has ever held**, and
with `via-col-square` (`src/L/Ordinal/SquareLaw.lagda.md:960-961`) the first
square law above `ω`. It also converts the campaign's open question from "how do
we get `Init`" into "how do we get `AmbCard`", which is a smaller and more
honest question.

**A NO-GO earns the obstruction, named at `file:line`.** If the fourth conjunct
does not follow from `AmbCard` plus the induction hypothesis, then the ambient
route is dead at its centre and the coded route is the only one, which nothing
has yet established. **A stated NO-GO is a full return and not a failure.**

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
  changed_files_any = ["agents/tasks/LJ-1-393/Probe393.agda"]
  changed_files_none = ["agents/tasks/LJ-1-393/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  error_class = "unsolved_meta"
  changed_files_any = ["agents/tasks/LJ-1-393/review-of-*.md"]

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
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 131.416)
- CANDIDATE dev/ARCHIVE.md  (score 103.305)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 84.052)
- CANDIDATE archive/dev/TASKS-archived.md  (score 72.458)
- CANDIDATE archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md  (score 68.781)

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/terms-2026-08.md  (score 44.103)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 43.557)
- CANDIDATE dev/literature/geology.md  (score 32.935)
- CANDIDATE dev/literature/devlin-II5.md  (score 28.211)
- CANDIDATE dev/literature/digest.md  (score 20.230)
