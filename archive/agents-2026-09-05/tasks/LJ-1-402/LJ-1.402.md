# LJ-1.402: the selected code, read back as an UNTRUNCATED ambient injection

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-402/Probe402.agda`.

    sel-arrow :
        (κ : S) (oκ : IsOrd (fst κ))
      → (nonempty : <the `Selected` module's own hypothesis, at its own type>)
      → ⟪ fst κ ⟫ ↪ ⟪ fst (InternalLeastCard.Selected.δᴸ κ oκ nonempty) ⟫

**UNTRUNCATED. No `∥ ∥₁` anywhere in the conclusion.** That is the whole point
of the task, and a truncated conclusion is a NO-GO, not a partial GO.

**IT TAKES `[LJ-1.401]`'s `sel-code` AS A MODULE HYPOTHESIS.** Do not import
that probe and do not rebuild it. State the hypothesis at the type
`[LJ-1.401]`'s report gives, exactly as `[LJ-1.396]` took `[LJ-1.392]`'s
`suc-absorb` (`agents/tasks/LJ-1-393/Probe393.agda` uses the same discipline for
`amb-limit`). **If `[LJ-1.401]` returned NO-GO, take `sel-code` as a BARE
hypothesis anyway and build the readback under it.** The readback is worth
measuring whether or not the gate opened, because it is the half nobody has
priced.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-402/Probe402.agda::sel-arrow"]

## SCOPE (write)
- agents/tasks/LJ-1-402/Probe402.agda
- agents/tasks/LJ-1-402/lj-1.402-report.md

## PREMISES
- `Small` takes exactly `InjCode`'s four conjuncts, in that order, and no other hypothesis. Basis: src/L/Coding/Injection.lagda.md:123-128
- It delivers the ambient function `small`, UNTRUNCATED. Basis: src/L/Coding/Injection.lagda.md:144
- It delivers that function's injectivity, UNTRUNCATED. Basis: src/L/Coding/Injection.lagda.md:147
- `InjCode F a b` reads `a` as the DOMAIN and `b` as the range, so `InjCode (up F) κ δᴸ` codes a map out of `κ` into `δᴸ`. Basis: src/L/Cardinal.lagda.md:223-228
- `_↪_` is a pair of a function and its injectivity, so `small` and `small-inj` are literally the two fields. Basis: src/L/Cardinal.lagda.md:47-48
- `L.Absorption` runs this exact readback at a delivered site, for the successor shift. Basis: src/L/Absorption.lagda.md:504
- The four conjuncts it feeds `Small` are built there and are the shape yours will be destructured to. Basis: src/L/Absorption.lagda.md:452-481
- Its range clause, the fourth conjunct. Basis: src/L/Absorption.lagda.md:493-497
- The ambient side of this same selection is truncated BY CONSTRUCTION and the chapter says why. Basis: src/L/Cardinal.lagda.md:132

## WHAT IS DELIVERED ALREADY

**THE READBACK, GENERIC, IN `src/`.** `module Small (F D C : S)` takes the four
conjuncts and returns `small` and `small-inj`
(`src/L/Coding/Injection.lagda.md:123-147`). It is generic in all three sets and
it names no stage, no cardinal and no tower.

**ITS ONE DELIVERED CALLER.** `L.Absorption` opens it at
`src/L/Absorption.lagda.md:504` and turns the successor shift's code into the
ambient `shiftFun` with `shiftFun-inj` (`:509-530`). **That caller is the
comparable for this task, and it is the only one in the tree.**

## WHAT IS MISSING

Nothing but the application. This task exists to MEASURE it, because the whole
route below depends on the readback being as cheap as it looks, and nobody has
run it at this site.

## THE REASONING

**THE TERM IS TWO PROJECTIONS, AND THE TASK IS TO FIND OUT WHAT ELSE IT COSTS.**

Destructure `[LJ-1.401]`'s `sel-code` into `F`, then the four conjuncts of
`InjCode (up F) κ δᴸ`. Open `Small (up F) κ δᴸ` with them. Then

    sel-arrow κ oκ ne = Sm.small , Sm.small-inj

**IF THAT IS THE WHOLE TERM, SAY SO AND REPORT THE NUMBER.** A six-line answer
is a first-class result here: it converts「the arrow is unreachable」into「the
arrow is two projections behind a proposition」, and that is the finding.

**WHAT WOULD MAKE IT NOT THE WHOLE TERM, AND YOU MUST CHECK EACH.**

1. `Small` may want its `F`, `D` and `C` at `S`, while `sel-code` hands over an
   `F` at `Mem (Lset β)`. `up` is the lift and `InternalLeastCard` already uses
   it inside `Good` (`src/L/Cardinal.lagda.md:240`). Measure whether the lift
   costs a line or a transport.
2. The four conjuncts arrive as ONE `InjCode` value. `Small` wants four
   arguments. That is a destructuring, and it is free unless the tuple's
   associativity fights you. Say which.
3. `small`'s type is `⟪ fst D ⟫ → ⟪ fst C ⟫` with `D` and `C` the L-elements you
   passed. If the conclusion needs `fst` juggling to match `_↪_`, that is a real
   line and it goes in the count.

**WHAT THIS DOES NOT GIVE YOU, AND DO NOT CLAIM IT.** It gives ONE arrow, out of
`κ` and into the internal least cardinal `δᴸ` that `InternalLeastCard.Selected`
picked. **It does not say `δᴸ` is a member of `κ`, and it does not say `δᴸ` is
infinite.** Both are `[LJ-1.403]`'s obligation. Without them this arrow is not
yet a descent, and a report that calls it one is wrong.

**W2 (DD4).** The term is sited at `InternalLeastCard` by its type and cannot be
written generically; `Small` is where the generic content already lives, and you
add none. Say exactly that in the report and name the one delivered generic
module you leaned on.

**W3, THE WIDEST UNMEASURED TERM.** It is item 1, the lift from
`Mem (Lset β)` to `S` across `Small`'s three set arguments. **The probe is
`up-lands`: state that lift alone at the three positions, run it, and report the
number of code lines before you write anything else.** ESTIMATE for the
obligation: about 8 code lines. BASIS: `shiftFun` and `shiftFun-inj`, a
delivered comparable of SHAPE at `src/L/Absorption.lagda.md:509-530`, where the
readback itself is two definitions and the surrounding lines are that site's own
value lemma, which you do not owe. **It is not a comparable of size and nothing
may be funded against it.**

## WHAT GO AND NO-GO EACH EARN

**A GO DELIVERS THE FIRST UNTRUNCATED ARROW THE CAMPAIGN HAS EVER HAD AT A
SELECTED CARDINAL**, and it prices it. Every route since `[LJ-1.394]` has been
blocked on exactly this object.

**A NO-GO EARNS THE STEP THAT FAILS, AT `file:line`.** If `Small` cannot be fed
from a selected code, that is a fact about the coding interface and the next
brief repairs the interface rather than the mathematics. **A stated NO-GO is a
full return.**

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
  changed_files_any = ["agents/tasks/LJ-1-402/Probe402.agda"]
  changed_files_none = ["agents/tasks/LJ-1-402/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  error_class = "unsolved_meta"
  changed_files_any = ["agents/tasks/LJ-1-402/review-of-*.md"]

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

## YOUR ROLE (program-generated, do not edit)

**You write the Agda this brief names, and the probe it names (A21).** The mathematician specifies; you build it and make it typecheck. Your report is the other half of that channel, so write what the next brief will need.

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
- CANDIDATE archive/src/2026-08-09-rud-route/L/Coding  (score 44.812)
- CANDIDATE archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md  (score 39.550)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 35.118)
- CANDIDATE archive/dev/TASKS-archived.md  (score 30.442)
- CANDIDATE dev/ARCHIVE.md  (score 26.001)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 57.230)
- CANDIDATE dev/literature/devlin-II5.md  (score 22.006)
- CANDIDATE dev/literature/terms-2026-08.md  (score 19.884)
- CANDIDATE dev/literature/digest.md  (score 17.115)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
