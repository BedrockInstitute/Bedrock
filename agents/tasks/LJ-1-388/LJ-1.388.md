# LJ-1.388: the internal product of two L-elements, and the ambient bridge into it

## HEAD
head_slot: mathematician
machine: shared

## THE OBLIGATION

Build ONE object and its bridge, in `agents/tasks/LJ-1-388/Probe388.agda`:

    prodL       : (a b : S) → S
    prod-bridge : (a b : S) → (⟪ fst a ⟫ × ⟪ fst b ⟫) ↪ ⟪ fst (prodL a b) ⟫

`prodL a b` is the L-element whose members are the Kuratowski pairs of a member
of `a` with a member of `b`. `prod-bridge` is the ambient injection from the
product of the two member types into the member type of that L-element.

**BUILD IT AT GENERIC `a` AND `b`, NEVER AT ONE ORDINAL.** A product of two
L-sets is generic by nature and a square of one ordinal is not, so the fixed
form here would be a DD4 defect and not a shortcut. Instantiating at `a := b :=
δ` is then one line, and that instance is the FIRST CONJUNCT of `Leg1`
(`agents/tasks/LJ-1-386/Probe386.agda:287-291`).

**If the L-membership half cannot be discharged, state the obstruction at
`file:line` and stop. Both answers discharge this task.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-388/Probe388.agda::prodL",
               "agents/tasks/LJ-1-388/Probe388.agda::prod-bridge"]

## SCOPE (write)
- agents/tasks/LJ-1-388/Probe388.agda
- agents/tasks/LJ-1-388/lj-1.388-report.md

## PREMISES
- `Leg1`'s first conjunct is exactly an ambient injection from the product of two member types into the member type of an L-element, and `leg1-gives-sq` closes the whole route from `Leg1` untruncated. Basis: agents/tasks/LJ-1-386/Probe386.agda:287-295
- `src/` holds no cartesian product of two L-sets today, so the object is unbuilt rather than mislaid. Basis: agents/tasks/LJ-1-386/lj-1.386-report.md:127-133
- The retired rud route delivered the AMBIENT product as a two-line `sett` whose index type is literally `⟪ x ⟫ × ⟪ y ⟫`, with its two-directional specification beside it. Basis: archive/src/2026-08-09-rud-route/L/Rud/Ops.lagda.md:210-221
- Replacement in L is delivered, and `module Range` is the delivered comparable of shape: ONE replacement with its functionality proof. Basis: src/L/Coding/Injection.lagda.md:186-218
- The ambient Kuratowski pair is injective, which is the whole content of the bridge's injectivity. Basis: src/V/Coding.lagda.md:178-179
- The retired route delivered a TRUNCATED square law and never an untruncated one, and its counting call site was RED, so the payoff this route aims at has never existed in this repository. Basis: archive/dev/TASKS-archived.md:78-82
- The door `[LJ-1.386]` measured returns an INJECTION and never a bijection, which is why it does not reopen what the archived chapter closed. Basis: archive/src/2026-08-09-rud-route/Everything.lagda.md:307-308
- `⟪ s ⟫` is not the `sett` index type: membership asks for a preimage MERELY, so a set built by replacement does not hand its index over. Basis: src/V/Hierarchy.lagda.md:45-49

## WHAT IS DELIVERED ALREADY
- `Leg1` and `leg1-gives-sq`, green: agents/tasks/LJ-1-386/Probe386.agda:287-302
- `code-untruncates`, the door, green at ARBITRARY `a` and `b`: agents/tasks/LJ-1-386/Probe386.agda:264-284
- Replacement in L: src/L/Axioms/Full.lagda.md:277
- Union and pairing in L: src/L/Axioms/Basic.lagda.md:634, src/L/Axioms/Basic.lagda.md:731
- The one-replacement comparable, with its functionality proof: src/L/Coding/Injection.lagda.md:186-218
- The ambient pair and its injectivity: src/V/Coding.lagda.md:178-179
- `_↪_`, the injection type this task must produce: src/L/Cardinal.lagda.md:47-48
- `Mem`, and `Lset→isL`, which lifts a member of a stage to an L-element: src/L/Choice/Step.lagda.md:217-218, src/L/Constructible.lagda.md:395-396

**FROM THE ARCHIVE, AND IT IS THE REASON THIS BRIEF IS CHEAP.** The retired rud
route built this object once already, ambiently:

- `F2`, the product itself, two lines: archive/src/2026-08-09-rud-route/L/Rud/Ops.lagda.md:210-211
- `F2-RHS` and `F2-spec`, the membership reading in both directions: archive/src/2026-08-09-rud-route/L/Rud/Ops.lagda.md:213-221
- `prod-out`, that a pair of members lands in the product: archive/src/2026-08-09-rud-route/L/Rud/SatSets.lagda.md:100-101
- `JF2`, the tower membership of the product, for the J tower: archive/src/2026-08-09-rud-route/L/Rud/SatSets.lagda.md:218-219

**READ THESE FIRST AND SAY WHAT YOU TOOK, at `file:line`.** The archived
construction is AMBIENT, so `F2` and `prod-out` may port nearly whole. `JF2` is
the tower half and it does NOT port: it reads the rud closure of the J tower,
which this route does not have. **The L-membership is the part you must build.**

## WHAT IS MISSING

Two things, and the second is the task.

1. **The membership reading**, that `pr u v ∈ˢ prodL a b` exactly when `u ∈ˢ a`
   and `v ∈ˢ b`. The archived `F2-spec` is this statement for the ambient `sett`
   form.
2. **`isL (fst (prodL a b))`, the L-membership.** `JF2` is the same fact for the
   J tower and it reads that tower's rud closure. This route has no rud closure.
   The delivered substitute is replacement in L, applied twice with a union, or
   a direct placement in a stage. **Which of the two is cheaper is unmeasured,
   and measuring it is half of what this task buys.**

## LAWS (built by hand, and the reason is a defect in the builder)

*R17's bundle. **The injector could not produce it.** `laws_bundle()` at
`scripts/pod/pod.py:979` runs `scripts/dispatch/rules.py`, and commit `061490d`
moved that file to `scripts/pod/rules.py`, so the producer returns None and
pre-flight P21 refuses every brief that does not already carry this block. The
text below is `.venv/bin/python scripts/pod/rules.py --for probe`, verbatim.
**The kind is `probe` by the work and not by the derivation:**
`kind_for_scope()` at `scripts/pod/rules.py:95-107` filters to `src/` paths
first, so a probe in a task directory derives `recon`, and AGENTS.md forbids
`src/` for a probe, which makes the `probe` branch unreachable. Both defects are
the maintainer's and neither is this task's.*

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

`[LJ-1.386]` measured the door and it is real: `code-untruncates`
(`agents/tasks/LJ-1-386/Probe386.agda:264-268`) takes a TRUNCATED coded
injection and returns ambient DATA, with no axiom past the `lem` the tree
already carries. It also refuted the brief it was given: the `Good` of
`src/L/Cardinal.lagda.md:187-190` names no target, so its internal existence is
free at every site and buys no descent
(`agents/tasks/LJ-1-386/lj-1.386-report.md:106-113`).

**So the route's remaining cost is `Leg1`, and `Leg1` has exactly two conjuncts.**
The second is the coded injection with values in `δ`, which is the cardinal
arithmetic. **The first is this task**, and `[LJ-1.386]` named it the widest
unmeasured term and named this probe as its measurement
(`agents/tasks/LJ-1-386/lj-1.386-report.md:254-266`).

**WHY THE FIRST CONJUNCT AND NOT BOTH.** The two conjuncts fail independently
and only one of them is cardinal arithmetic. Building the product first tells
the route whether the CHEAP half is cheap, at a price the second half cannot
hide. `leg1-gives-sq` already closes everything after `Leg1`, so nothing
downstream has to be rebuilt to consume this.

**WHAT THE PAYOFF IS, AND THE ARCHIVE SAYS IT HAS NEVER EXISTED HERE.**
`leg1-gives-sq` returns `sq (fst δ)` UNTRUNCATED, and `sq` is an INJECTION and
not a bijection (`src/L/Ordinal/SquareLaw.lagda.md:685-687`). The retired route
delivered the TRUNCATED law only: `archive/dev/TASKS-archived.md:82` records
`L3.32-T47`,「Truncated square law at initial ordinals」, DELIVERED, while
`archive/dev/TASKS-archived.md:78` records `L3.32-T43`,「Where counting calls the
square law」, RED, wall confirmed. **So this route aims at an object the
repository has never held.** `[LJ-1.386]` also measured the limit that keeps the
two apart: its door returns an injection, and the archived chapter closed a
BIJECTION (`archive/src/2026-08-09-rud-route/Everything.lagda.md:307-308`).
**Do not report a bijection, an equivalence or a cure for either wall.** Report
the injection you built and nothing wider.

**NO PRICE IS CARRIED INTO THIS BRIEF, AND W3 IS WHY.** `[LJ-1.386]` measured
that no size basis exists: the nearest delivered comparable, `module Range` at
`src/L/Coding/Injection.lagda.md:186-218`, is 33 lines for ONE replacement, and
it is a comparable of SHAPE and not of SIZE, because a product needs two nested
replacements and a pair-membership reading
(`agents/tasks/LJ-1-386/lj-1.386-report.md:256-264`). **Do not transfer that 33
into a number.** This probe is the measurement, and its report is where the
first honest figure for this object appears.

**THE ARCHIVED `F2` CHANGES THE SHAPE, NOT THE PRICE.** `F2` is a `sett` with
index `⟪ x ⟫ × ⟪ y ⟫`, so the AMBIENT product and its bridge may be nearly free:
the bridge's target would then be the member type of that `sett`. **But `sett`
membership asks for a preimage merely** (`src/V/Hierarchy.lagda.md:45-49`), and
`isL` is the thing the archived form gives no help with. **Try the archived
ambient form FIRST and price its L-membership; if that stalls, fall back to two
nested replacements, whose output is an L-element by construction and whose
bridge is then the expensive half.** Report which you tried, in which order, and
what each cost.

**THE LITERATURE SAYS THE PRODUCT IS NOT FREE, AND THAT IS THE ONE THING IT
SAYS.** `dev/literature/rudimentary-functions.md:68` lists `F2(x, y) = x x y` as
one of the rudimentary BASIS operations, and `:144` records Devlin's `BS` as
`ReS0 + Cartesian product + full foundation + omega in V`. **So the product is a
named primitive in the weak systems and not a consequence of the weaker ones.**
Expect the L-membership half to cost something. **Nothing in the digest tells
you how to build it from replacement**, which is this route's own machinery, so
the digest prices nothing here and you should not read it for a method.

**TWO CAUTIONS, AND BOTH ARE MEASURED.**

1. **Do not fix the site.** `[LJ-1.386]` measured that nothing in the tree
   certifies `+ω ω` as a band ordinal, and that `+ω` has zero consumers in
   `src/` (`agents/tasks/LJ-1-386/lj-1.386-report.md:207-232`). A product built
   at that one ordinal would inherit that doubt for nothing. **Build at generic
   `a` and `b` and the doubt does not arise.**
2. **`[LJ-1.386]` was re-dispatched on 2026-08-19 at 05:00:04Z and may still be
   writing.** Its accept failed on `spec_surface`, an infrastructure class, not
   on its mathematics. **Re-read `Probe386.agda` and its report before you trust
   any line number this brief takes from them**, and say in your return whether
   the lines still say what this brief says they say. Every `src/` and
   `archive/` citation above is outside that task's write scope and is stable.

## WHAT GO AND NO-GO EACH EARN

**A GO earns the first honest price for the internal product**, and it converts
`Leg1` from two unbuilt conjuncts into one. It would also tell the route whether
the archived rud construction ports across the route change, which no dispatch
has measured and which bears on far more than this task.

**A NO-GO earns the obstruction to `isL` on a product, named at `file:line`.**
That is worth as much and costs less: it would say that the internalization
route cannot form a product of two L-elements from delivered machinery, which is
a fact about the route and not about this probe. A NO-GO must say what would
have to change to move the obstruction. **A stated NO-GO is a full return and
not a failure.**

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
  changed_files_any = ["agents/tasks/LJ-1-388/Probe388.agda"]
  changed_files_none = ["agents/tasks/LJ-1-388/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  error_class = "unsolved_meta"
  changed_files_any = ["agents/tasks/LJ-1-388/review-of-*.md"]

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
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 240.538)
- CANDIDATE dev/ARCHIVE.md  (score 207.646)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 180.125)
- CANDIDATE archive/dev/TASKS-archived.md  (score 158.623)
- CANDIDATE archive/src/2026-08-09-rud-route/Everything.lagda.md  (score 75.893)

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 82.001)
- CANDIDATE dev/literature/devlin-II5.md  (score 62.326)
- CANDIDATE dev/literature/terms-2026-08.md  (score 55.195)
- CANDIDATE dev/literature/digest.md  (score 41.646)
- CANDIDATE dev/literature/formalizations-landscape.md  (score 33.102)
