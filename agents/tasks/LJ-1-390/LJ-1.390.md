# LJ-1.390: the descent route to `sq`, priced against `Leg1`'s second conjunct

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build TWO terms in `agents/tasks/LJ-1-390/Probe390.agda`, at GENERIC `δ` and
`κ`:

    descent-gives-sq : (δ κ : S)
                     → ⟪ fst κ ⟫ ↪ ⟪ fst δ ⟫
                     → sq (fst κ)
                     → ∥ Σ[ A ∈ Mem (Lset (SiteBound.β δ)) ]
                           InjCode (SiteBound.up δ A) δ κ ∥₁
                     → sq (fst δ)

    descent-closes : descent-owes
                   → (δ : S) → ⟨ fst δ ∈ˢ sucV α₀ ⟩
                   → (⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥)
                   → sq (fst δ)

`descent-gives-sq` is the descent route's payoff. It takes the square law at a
SMALLER ordinal `κ`, the inclusion of `κ` in `δ` as an ambient injection, and a
TRUNCATED coded injection from `δ` into `κ`. It returns `sq (fst δ)`
untruncated. **IT USES NO INTERNAL PRODUCT.** It is the exact analogue of
`leg1-gives-sq` (`agents/tasks/LJ-1-386/Probe386.agda:294-295`) on a different
route.

`descent-owes` is a type you write. It names what the descent route still owes.
`descent-closes` then assembles the whole discharge from it, by `∈-induction`.

**THREE CLAUSES BIND `descent-owes`, AND THEY EXIST TO STOP ONE GAME.** A
residue type that holds the conclusion makes `descent-closes` vacuous and
measures nothing.

1. **It is CLOSED.** It takes no parameter from `descent-closes`'s telescope.
2. **It never applies `sq` to a variable that `descent-closes` binds.** It may
   apply `sq` to an internal cardinal it quantifies over itself.
3. **The report gives ONE line that says why it is not the conclusion in
   disguise.**

**If either term cannot be built, state the obstruction at `file:line` and
stop. Both answers discharge this task.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-390/Probe390.agda::descent-gives-sq",
               "agents/tasks/LJ-1-390/Probe390.agda::descent-closes"]

## SCOPE (write)
- agents/tasks/LJ-1-390/Probe390.agda
- agents/tasks/LJ-1-390/lj-1.390-report.md

## PREMISES
- The consumer takes `sq` as a MODULE PARAMETER quantified over every `δ` with `δ ∈ˢ sucV α₀` and `δ ∉ ω`. It carries NO `Init` hypothesis, so a discharge must serve an arbitrary `δ`. Basis: src/L/StageCardinal.lagda.md:17-20
- The parameter is applied at an arbitrary `α` inside the chapter, which is where the demand is spent. Basis: src/L/StageCardinal.lagda.md:283
- `via-col-square` supplies `sq` ONLY under `Init`, so it cannot discharge that parameter alone. Basis: src/L/Ordinal/SquareLaw.lagda.md:960-961
- `Init` is four conjuncts and its second is `⟨ ω ∈ˢ α ⟩`. The tree already records that `Init ω` is refuted by `∈-irrefl`, so the residue band is not empty and its first member is `ω`. Basis: src/L/InjChain.lagda.md:104
- `sq ω` is DELIVERED and needs no route, so `ω` itself is already covered. Basis: src/L/InjChain.lagda.md:184-185
- `code-untruncates` takes a TRUNCATED coded injection at ARBITRARY `a` and `b` and returns ambient DATA. It is green. Basis: agents/tasks/LJ-1-386/Probe386.agda:264-268
- `IsCardinalL` is the tree's own coded cardinality predicate: no member of `κ` admits a code for an injection out of `κ`. Basis: src/L/Cardinal.lagda.md:230-233
- `InternalLeastCard.Selected.δ-inj` already carries the truncated coded injection in the SHAPE that `code-untruncates` consumes, at `a := κ`. Basis: src/L/Cardinal.lagda.md:257-258
- `∈-induction` is delivered, so a recursion down the membership order needs no new well-foundedness. Basis: src/V/Hierarchy.lagda.md:177-180
- `Leg1`'s second conjunct is a coded injection from the internal square `P` into `δ`, and `[LJ-1.386]` named it the only place cardinal arithmetic enters the route. Basis: agents/tasks/LJ-1-386/lj-1.386-report.md:138-139
- `src/` holds NO cartesian product of two L-sets, so the product route must build one first. Basis: agents/tasks/LJ-1-386/lj-1.386-report.md:130-136
- The archived route reached the ordinal pairing well-order and its order-type reading, and stalled on exactly the equinumerosity the square law states. Basis: archive/src/2026-08-09-rud-route/L/Ordinal/Pairing.lagda.md:4-16

## WHAT IS DELIVERED ALREADY
- `code-untruncates`, green at arbitrary `a` and `b`: agents/tasks/LJ-1-386/Probe386.agda:264-284
- `Leg1` and `leg1-gives-sq`, green, the product route's payoff: agents/tasks/LJ-1-386/Probe386.agda:287-302
- `sq` and `Init`: src/L/Ordinal/SquareLaw.lagda.md:685-698
- `via-col-square`, the `Init`-restricted supply: src/L/Ordinal/SquareLaw.lagda.md:960-961
- `squareω`, the supply at `ω`: src/L/InjChain.lagda.md:184-185
- `InjCode` and `IsCardinalL`: src/L/Cardinal.lagda.md:223-233
- `SiteBound`, which fixes `β` and `up` for a given `a`: src/L/Cardinal.lagda.md:163
- `InternalLeastCard`, the internal least cardinal and its truncated code: src/L/Cardinal.lagda.md:235-258
- `orderAt`, `leastOf` and `Small`, the three pieces `code-untruncates` spends: src/L/Choice/Step.lagda.md:730, src/L/WellOrder/Base.lagda.md:158, src/L/Coding/Injection.lagda.md:123
- `∈-induction`: src/V/Hierarchy.lagda.md:177-180
- `_↪_`, the injection type both routes produce: src/L/Cardinal.lagda.md:47-48
- A module header that already opens every one of these: agents/tasks/LJ-1-386/Probe386.agda:29-50

## WHAT IS MISSING

**Nobody has priced the descent route.** Every dispatch since `[LJ-1.384]` has
priced ONE route: build the internal square `P`, bridge the ambient product into
it, and code an injection from `P` into `δ`. `[LJ-1.388]` is building the first
conjunct of that route now.

The descent route asks a different question. It never forms a product of two
L-sets. It moves the square law DOWN to the cardinal of `δ` and back:

    ⟪δ⟫ × ⟪δ⟫  ↪  ⟪κ⟫ × ⟪κ⟫  ↪  ⟪κ⟫  ↪  ⟪δ⟫

The first step is `code-untruncates δ κ` applied twice. The second step is
`sq (fst κ)`. The third is the inclusion of `κ` in `δ`.

**Three things are missing and the first two are this task.**

1. **`descent-gives-sq`.** The composition above, as one term.
2. **`descent-closes`, and with it the honest statement of `descent-owes`.**
   The recursion must reach a `κ` where `sq` is supplied. `squareω` supplies it
   at `ω` and `via-col-square` supplies it under `Init`. **Whether an internal
   cardinal is `Init` is NOT delivered**, and that gap is the likely content of
   `descent-owes`.
3. **A price for each route, side by side.** That is the report's job.

## LAWS (built by hand, and the reason is a defect in the builder)

*R17's bundle. **The injector could not produce it.** `laws_bundle()` at
`scripts/pod/pod.py:959` reads `scripts/dispatch/rules.py`, and commit `061490d`
moved that file to `scripts/pod/rules.py`, so the producer returns None and
pre-flight P21 refuses every brief that does not already carry this block. RE-
MEASURED 2026-08-19 for this brief: the path at `scripts/pod/pod.py:979` still
reads `"dispatch"`, so the defect stands. The text below is
`.venv/bin/python scripts/pod/rules.py --for probe`, verbatim. **The kind is
`probe` by the work and not by the derivation:** `kind_for_scope()` at
`scripts/pod/rules.py:95-107` filters to `src/` paths first, so a probe in a
task directory derives `recon`, and AGENTS.md forbids `src/` for a probe. Both
defects are the maintainer's and neither is this task's.*

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

**THE DOOR IS ROUTE-NEUTRAL AND THE ROUTE THAT USES IT IS NOT.**
`code-untruncates` takes `(a b : S)` and returns `⟪ fst a ⟫ ↪ ⟪ fst b ⟫`
(`agents/tasks/LJ-1-386/Probe386.agda:264-268`). `[LJ-1.386]` spent it at
`a := P`, `b := δ`, which needs the internal square `P` to exist first. **The
same door at `a := δ`, `b := κ` needs no product at all.** This brief asks what
that costs.

**WHY THE DESCENT ROUTE MIGHT BE CHEAPER, IN ONE SENTENCE.** The product route
must first BUILD an object the tree does not hold, and `[LJ-1.386]` measured
that absence directly: `src/` has no cartesian product of two L-sets
(`agents/tasks/LJ-1-386/lj-1.386-report.md:130-136`). The descent route builds
no set. It composes four delivered arrows.

**WHY IT MIGHT BE MORE EXPENSIVE, AND THIS IS THE PART TO MEASURE FIRST.** The
descent bottoms out at an internal cardinal, and there `sq` must come from
somewhere. Two suppliers exist and NEITHER is known to serve an internal
cardinal:

- `squareω` serves `ω` and nothing else (`src/L/InjChain.lagda.md:184-185`).
- `via-col-square` serves an `Init` ordinal
  (`src/L/Ordinal/SquareLaw.lagda.md:960-961`), and `Init`'s fourth conjunct
  forbids an AMBIENT injection of the index into a member's square
  (`src/L/Ordinal/SquareLaw.lagda.md:696-698`), while `IsCardinalL` forbids only
  a CODED one (`src/L/Cardinal.lagda.md:230-233`).

**THE TWO PREDICATES POINT OPPOSITE WAYS AND THAT IS THE WHOLE RISK.**
`code-untruncates` carries a code to an ambient function. `IsCardinalL → Init`
needs the CONVERSE: an ambient function must produce a code. **Nothing measured
says that converse holds.** **If it does not hold, say so and stop.** A NO-GO
here is worth more than a GO, because it would rule the descent route out on
evidence and leave the product route the only one, which nothing has yet
established.

**DO NOT ASSUME `descent-owes` IS THAT CONVERSE.** It may be weaker. The
recursion needs `sq` at the cardinal, not `Init` at the cardinal. Find the
weakest statement that closes `descent-closes` and name it.

**THE ARCHIVE SAYS THIS EXACT WALL IS OLD.** The retired route built the
ordinal pairing well-order and the order-type reading of it, and named the
equinumerosity as "the one remaining theorem"
(`archive/src/2026-08-09-rud-route/L/Ordinal/Pairing.lagda.md:4-16`). **So a
report that claims to have closed the square law at a non-initial ordinal is
claiming something this repository has never held.** Report the injection you
build and nothing wider. Do not report a bijection and do not report an
equivalence.

**THE LITERATURE CARRIES NO METHOD FOR THIS, AND THAT IS MEASURED.** The
digest cites the square law as a BOUND and never proves it:
`dev/literature/terms-2026-08.md:290-293` reads「cited as a bound, not proved as
a theorem」. The nearest digested cardinal arithmetic is Devlin's 1.1(vii),
which `dev/literature/devlin-II5.md:357-358` lists as an UNDIGESTED dependency
of 5.5. **So do not spend time reading the digest for a construction. Read it
only to check a statement you already have.** Name in a LITERATURE USED section
what you read, and WHY NOT for what you skipped.

**DO NOT WAIT FOR `[LJ-1.388]` AND DO NOT DUPLICATE IT.** `[LJ-1.388]` is
building the internal product at generic `a` and `b`. Its product is useful
whatever this task returns, and this task needs none of it. **Write nothing
under `agents/tasks/LJ-1-388/`.**

**W2 AND DD4.** Build at GENERIC `δ` and `κ`. A descent stated at one ordinal
measures one ordinal. `[LJ-1.386]` measured that nothing in the tree certifies
`+ω ω` as a band ordinal and that `+ω` has zero consumers in `src/`
(`agents/tasks/LJ-1-386/lj-1.386-report.md:213-217`), so a fixed site would
inherit that doubt for nothing.

**W3, AND NO PRICE IS CARRIED IN.** The nearest comparable is
`leg1-gives-sq`, which is 9 lines for the product route's payoff
(`agents/tasks/LJ-1-386/Probe386.agda:294-302`). **It is a comparable of SHAPE
and not of size**: it composes two arrows and `descent-gives-sq` composes four.
**Do not transfer that number.** This probe is the measurement.

**WRITE THE REPORT FIRST AND FILL IT AS YOU GO** (C-22). Run the probe while
this task is live. Nothing typechecks it after the task closes.

## WHAT GO AND NO-GO EACH EARN

**A GO earns the first price for the descent route and a side-by-side
comparison with the product route.** It would tell the campaign which of two
routes to fund, which no dispatch has ever been able to say.

**A NO-GO earns the obstruction to the descent, named at `file:line`.** The
likely obstruction is that an ambient injection cannot produce a code, and that
would be a fact about the whole coded route and not about this probe. A NO-GO
must say what would have to change to move it. **A stated NO-GO is a full
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
  changed_files_any = ["agents/tasks/LJ-1-390/Probe390.agda"]
  changed_files_none = ["agents/tasks/LJ-1-390/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  error_class = "unsolved_meta"
  changed_files_any = ["agents/tasks/LJ-1-390/review-of-*.md"]

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
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 30.315)
- CANDIDATE archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md  (score 30.118)
- CANDIDATE archive/src/2026-08-09-rud-route/L/Ordinal/Pairing.lagda.md  (score 26.098)
- CANDIDATE archive/src/2026-08-09-rud-route/L/CardinalCount.lagda.md  (score 20.155)
- CANDIDATE archive/src/2026-08-09-rud-route/Everything.lagda.md  (score 19.273)

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/terms-2026-08.md  (score 14.687)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 12.986)
- CANDIDATE dev/literature/rudimentary-functions.md  (score 8.889)
- CANDIDATE dev/literature/devlin-errata.md  (score 8.037)
- CANDIDATE dev/literature/devlin-II5.md  (score 7.254)
