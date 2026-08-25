# LJ-1.392: the successor absorption, and `Init`'s limit clause from it

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build TWO terms in `agents/tasks/LJ-1-392/Probe392.agda`, at a GENERIC ordinal.

    suc-absorb : (γ : V ℓ) → IsOrd γ → ⟨ ω ∈ γ ⟩ → ⟪ sucV γ ⟫ ↪ ⟪ γ ⟫

    amb-limit : (α : V ℓ) → IsOrd α → ⟨ ω ∈ α ⟩
              → ((β : V ℓ) → IsOrd β → ⟨ β ∈ α ⟩ → ⟨ ω ∈ β ⟩
                           → (⟪ α ⟫ ↪ ⟪ β ⟫) → Empty.⊥)
              → (γ : V ℓ) → ⟨ γ ∈ α ⟩ → ⟨ sucV γ ∈ α ⟩

`suc-absorb` is the hotel shift. An infinite ordinal absorbs one new point,
because it holds a copy of `ω` to shift along.

**THIS TERM IS ALREADY BUILT, IN THE ARCHIVE, AND THIS TASK IS A PORT.** Read
`module Shift` at
`archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:652-767` BEFORE
you write a line. It carries `shift` (`:693-694`), `shift-inj` (`:730-767`) and
the three case lemmas, at a generic infinite ordinal, and its prose states the
theorem in the same words this brief does (`:640-646`). **W4 binds you: price
the ideal form written fresh today, then compare it with the archived chapter,
and report both numbers.** A port that is cheaper is the right answer and so is
a fresh write that is cheaper. **Say which you did and why.**

`amb-limit` is `Init`'s THIRD conjunct (`src/L/Ordinal/SquareLaw.lagda.md:695`),
discharged from an ambient no-injection hypothesis. `suc-absorb` is what makes
it go through, and it is the only place `suc-absorb` is spent here.

**THE SHAPE OF `suc-absorb`, AND THE ARCHIVE ALREADY FIXES IT.** `sucV γ` holds
the members of `γ` and `γ` itself (`src/V/Model.lagda.md:218-237`). Send `γ` to
the numeral `0` inside `γ`. Send a member that lies in `ω` to its own successor
numeral. Send every other member to itself. The archived `shift-dec`
(`archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:686-694`)
decides the two cases by `lem` twice, and it recovers the numeral index by
`leastOf natSWO` (`:663-664`), NOT by `PT.rec`. **That is the cure for the
truncation trap named below, and it is delivered.**

**THE SHAPE OF `amb-limit`, AND IT IS SHORTER THAN IT LOOKS.** Split on whether
`γ` is finite. When `γ ∈ ω`, `ω-limit` gives `sucV γ ∈ ω`
(`src/L/InjChain.lagda.md:109-110`) and `ω ∈ α` carries it into `α` by the
ordinal's own transitivity. When `γ` is infinite, take `ord-tri` on `α` and
`sucV γ` (`src/L/Ordinal/Linear.lagda.md:136`). **Two of the three cases die on
`∈-irrefl` alone** (`src/V/Hierarchy.lagda.md:155`), and only `α ≡ sucV γ` needs
`suc-absorb`.

**If either term cannot be built, state the obstruction at `file:line` and
stop. Both answers discharge this task.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-392/Probe392.agda::suc-absorb",
               "agents/tasks/LJ-1-392/Probe392.agda::amb-limit"]

## SCOPE (write)
- agents/tasks/LJ-1-392/Probe392.agda
- agents/tasks/LJ-1-392/lj-1.392-report.md

## PREMISES
- `Init`'s third conjunct is successor closure, and nothing in the tree derives it from a cardinality hypothesis. Basis: src/L/Ordinal/SquareLaw.lagda.md:692-700
- `InitialCore` takes that clause as a module PARAMETER, so the chapter was built to consume it and never to produce it. Basis: src/L/Ordinal/SquareLaw.lagda.md:703-709
- The ONE delivered instance supplies the three clauses at `ω` only, and its no-injection clause is vacuous there. Basis: src/L/InjChain.lagda.md:171
- That vacuity is stated in one line: no member of `ω` contains `ω`. Basis: src/L/InjChain.lagda.md:123-126
- `ω-limit` already gives successor closure INSIDE `ω`, so the finite case of `amb-limit` is delivered. Basis: src/L/InjChain.lagda.md:109-110
- `sucV` membership splits into the two cases this construction needs. Basis: src/V/Model.lagda.md:218-237
- `ord-tri` gives the ordinal trichotomy `lem` needs. Basis: src/L/Ordinal/Linear.lagda.md:136
- `∈-irrefl` kills the two easy trichotomy branches. Basis: src/V/Hierarchy.lagda.md:155
- A member of `ω` is merely a numeral, which is what the shift reads. Basis: src/L/StageCardinal.lagda.md:422-423
- `numeral-ord` and `numeral-mem` carry a numeral and its membership. Basis: src/L/Ordinal.lagda.md:244-253
- `#-inj′` gives numeral injectivity, which the shift's injectivity needs. Basis: src/V/Coding.lagda.md:114-115
- `fiber`, `member` and `↪-inj` are the three presentation lemmas every ambient injection in this tree is built from. Basis: src/V/Presentation.lagda.md:31-38
- `numeral-into-ω` and its injectivity are a delivered comparable of the same kind, built by the same three lemmas. Basis: src/L/InjChain.lagda.md:129-138
- `_↪_`, the injection type. Basis: src/L/Cardinal.lagda.md:47-48
- THE ARCHIVED ROUTE ALREADY BUILT THIS SHIFT, at a generic infinite ordinal, and stated the theorem in prose. Basis: archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:640-646
- The archived `shift` and its injectivity. Basis: archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:693-694
- The archived numeral recovery goes through `leastOf natSWO` and not through `PT.rec`, which is the cure for the truncation trap. Basis: archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:663-664
- The archived route also spent the shift for the square law's SUCCESSOR STEP, which is not this task and is worth knowing. Basis: archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:787-800

## WHAT IS DELIVERED ALREADY
- `Init` and `InitialCore`: src/L/Ordinal/SquareLaw.lagda.md:692-709
- `Coreω`, the only instance, at `ω`: src/L/InjChain.lagda.md:171
- `ω-limit`, `ω∉β`, `noinj²ω`, `finite-excl-ω`: src/L/InjChain.lagda.md:109-169
- `numeral-into-ω` and `numeral-into-ω-inj`, the shift's nearest comparable: src/L/InjChain.lagda.md:129-138
- `∈sucV-elim`, `∈sucV-inl`, `self∈sucV`: src/V/Model.lagda.md:218-237
- `ord-tri`: src/L/Ordinal/Linear.lagda.md:136
- `suc∈or≡`, the successor-or-equal reading of the trichotomy: src/L/Ordinal/Stages.lagda.md:139
- `∈-irrefl`: src/V/Hierarchy.lagda.md:155
- `ω-mem→numeral`: src/L/StageCardinal.lagda.md:422-423
- `mem-ord`, `numeral-ord`, `numeral-mem`: src/L/Ordinal.lagda.md:221-253
- `fiber`, `member`, `↪-inj`: src/V/Presentation.lagda.md:31-38
- A probe header that already opens most of these: agents/tasks/LJ-1-390/Probe390.agda:29-50
- **THE WHOLE OF `suc-absorb`, in the archive**: archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:652-767
- The archived successor step that consumed it: archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:787-800

## WHAT IS MISSING

**THE TREE HOLDS NO CARDINAL ARITHMETIC AT ALL ABOVE `ω`.** `Coreω`
(`src/L/InjChain.lagda.md:171`) supplies `InitialCore`'s three hypotheses at `ω`
and nowhere else, and two of the three are vacuous there: `noinj²ω` is the
one-line observation that no member of `ω` contains `ω`
(`src/L/InjChain.lagda.md:123-126`). **So the chapter has one instance and that
instance measures nothing about a general ordinal.**

**`Init` HAS NO PRODUCER, RE-MEASURED 2026-08-19 BY `[LJ-1.390]`.** Seven lines
in `src/` name `Init` and none of them builds one
(`agents/tasks/LJ-1-390/lj-1.390-report.md:20-27`). `[LJ-1.286]` measured the
same absence before it.

**THIS TASK BUILDS THE ONE CLAUSE THAT NEEDS A NEW FACT.** Of `Init`'s four
conjuncts, the first two are hypotheses, the fourth is `[LJ-1.393]`'s job, and
the third needs an arithmetic fact the LIVE tree does not hold. **That fact is
`suc-absorb` and this task is where it lands.**

**WHAT IS MISSING IS THE FACT IN THE LIVE TREE, AND NOT THE MATHEMATICS.** The
archived route holds the whole shift
(`archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:652-767`), so
this task carries NO mathematical risk that the archive has not already
retired. **What it carries is a port risk**, and that risk is real: the archived
chapter sits over the retired route's own `S`, its own `natSWO` and its own
`leastOf`, and nothing says those resolve the same way in the live tree.
**Measure that, name every import that did not carry across, and report it.**
`amb-limit` is the genuinely new half.

## THE REASONING

**START WITH `amb-limit` AND WORK BACKWARDS.** Write `amb-limit` with
`suc-absorb` as a hole first. That fixes the exact statement `suc-absorb` must
have, and it tells you at once whether the two easy trichotomy branches really
die on `∈-irrefl`. If they do not, the shape of this task is wrong and you should
say so and stop.

**READ THE ARCHIVE BEFORE YOU WRITE, AND THE BOUNDARY MAKES THAT A RULE.** The
archived chapter is the answer to most of this task. Reading
`archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:640-767` costs
minutes and rebuilding it costs the task.

**THE TRUNCATION IS WHERE THIS WOULD HAVE GONE WRONG, AND THE ARCHIVE ALREADY
SOLVED IT.** `ω-mem→numeral` returns a MERE numeral
(`src/L/StageCardinal.lagda.md:422-423`) and `suc-absorb` must return a
FUNCTION, which is data. **A `PT.rec` into that goal does not typecheck.** The
archived cure is `numeralOf`, which recovers the index by `leastOf natSWO` over
the propositional predicate `v ≡ # k`
(`archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:663-664`), and
`numeralOf-uniq` (`:679-680`) is what makes the choice irrelevant. **Check that
`natSWO` and `leastOf` resolve in the live tree before you plan around them**,
and if either does not, say so at `file:line` and stop.

**W2 AND DD4.** Both terms are generic in the ordinal. Nothing here may name
`ω · 2`, `+ω` or any other site. `[LJ-1.386]` measured that nothing in this tree
certifies `+ω ω` as a band ordinal
(`agents/tasks/LJ-1-386/lj-1.386-report.md:211-236`), so a fixed site would
inherit that doubt for nothing.

**W3, THE WIDEST UNMEASURED TERM AND ITS PROBE. THE ARCHIVE MOVED IT.** The
widest unmeasured term is NO LONGER the shift, because the archive built it. It
is **whether the archived module's own supports resolve in the live tree**:
`natSWO`, `leastOf`, `isSetS`, `∈sucV-elim` and the `S` the archived chapter is
written over. **The probe is the import head alone**: write the archived
module's imports against the live tree and typecheck an empty body, BEFORE you
port a proof. Report every import that did not carry and what replaced it.

**THE ESTIMATE IS A PORT PRICE AND NOT A WRITE PRICE.** The archived `Shift` is
116 raw lines (`archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:652-767`)
and `amb-limit` is new. **About 25 code lines for `amb-limit`, on the basis of a
delivered comparable of SHAPE**: the chapter's own `ord-tri` split at
`src/L/StageCardinal.lagda.md:543-548` is the same three-branch shape.
**`suc-absorb` is UNPRICED by this brief, because the port price is what you
are being asked to measure.** **Do not fund anything against 25.**

**WRITE THE REPORT FIRST AND FILL IT AS YOU GO** (C-22). Run the probe while
this task is live. Nothing typechecks it after the task closes.

**REPORT THE NUMBER YOU MEASURED.** Give the wall seconds at the caliber the
program set on your pane, as the median of three consecutive runs, and give the
empty-module floor on the same machine on the same day.

## WHAT GO AND NO-GO EACH EARN

**A GO earns the live tree's first cardinal arithmetic above `ω`, one of
`Init`'s four conjuncts, and a measured port price for the archived chapter.**
`[LJ-1.393]` then needs only the fourth conjunct to produce the first `Init` the
live tree has ever held. **The port price is worth as much as the term**,
because the archived route holds more chapters that this campaign may want and
nobody has measured what one of them costs to bring across.

**A NO-GO earns the obstruction to successor absorption, named at `file:line`.**
That would say the ambient route to `Init` is blocked at its cheapest clause,
which is strong evidence that the whole ambient route is wrong and that the
campaign must run on codes. **A stated NO-GO is a full return and not a
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
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-392/Probe392.agda"]
  changed_files_none = ["agents/tasks/LJ-1-392/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  error_class = "unsolved_meta"
  changed_files_any = ["agents/tasks/LJ-1-392/review-of-*.md"]

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
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 181.566)
- CANDIDATE dev/ARCHIVE.md  (score 133.915)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 120.195)
- CANDIDATE archive/dev/TASKS-archived.md  (score 98.604)
- CANDIDATE archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md  (score 77.331)

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 59.362)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 57.082)
- CANDIDATE dev/literature/terms-2026-08.md  (score 46.463)
- CANDIDATE dev/literature/digest.md  (score 42.370)
- CANDIDATE dev/literature/geology.md  (score 41.141)
