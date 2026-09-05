# LJ-1.399: what does it cost to CODE one delivered ambient map? Measured at omega

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build TWO terms in `agents/tasks/LJ-1-399/Probe399.agda`.

    omega-pair-code : ∥ Σ[ A ∈ Mem (Lset (SiteBound.β (prodL ωL ωL))) ]
                          InjCode (SiteBound.up (prodL ωL ωL) A) (prodL ωL ωL) ωL ∥₁

    omega-leg1 : sq ω

`ωL` is `ω` as an L-element. `prodL` and `prod-bridge` are `[LJ-1.388]`'s terms
(`agents/tasks/LJ-1-388/Probe388.agda:296` and `:299`). **Take both as module
hypotheses and do not import that probe.**

**`omega-leg1` PROVES NOTHING NEW AND YOU MUST SAY SO IN THE REPORT.** `sq ω` is
delivered as `squareω` (`src/L/InjChain.lagda.md:184-185`). The term exists to
check MECHANICALLY that the code you built has the shape the door consumes, by
running `omega-pair-code` through the door and the bridge and landing in the
delivered type. **Build it with the door, never with `squareω`.** A report that
presents `omega-leg1` as a new theorem is wrong.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-399/Probe399.agda::omega-pair-code",
               "agents/tasks/LJ-1-399/Probe399.agda::omega-leg1"]

## SCOPE (write)
- agents/tasks/LJ-1-399/Probe399.agda
- agents/tasks/LJ-1-399/lj-1.399-report.md

## PREMISES
- The second conjunct of `Leg1` is a truncated CODED injection out of the internal square, and it is the only unpaid conjunct of the coded route. Basis: agents/tasks/LJ-1-386/Probe386.agda:288-290
- `[LJ-1.388]` delivered the internal product and the ambient bridge into it, at generic arguments, and stated that it says nothing about the coded injection. Basis: agents/tasks/LJ-1-388/lj-1.388-report.md:236-241
- `[LJ-1.388]` named this task's probe: one dispatch that builds an `InjCode` from the product into the ordinal, at ONE site. Basis: agents/tasks/LJ-1-388/lj-1.388-report.md:239-243
- Its estimate was about 130 code lines, on a comparable of shape and not of size, and it forbids quoting that number as a price. Basis: agents/tasks/LJ-1-388/lj-1.388-report.md:243-248
- `IdGraph` codes ONE ambient map, the identity, with its three satisfaction facts and its placement. It is the delivered comparable for a coding job. Basis: agents/tasks/LJ-1-386/Probe386.agda:94-193
- The door consumes exactly the shape this task builds. Basis: agents/tasks/LJ-1-386/Probe386.agda:264-268
- `InjCode`'s four conjuncts are three satisfaction facts plus a range clause. Basis: src/L/Cardinal.lagda.md:223-228
- `Small` reads a code back to an ambient injection. Basis: src/L/Coding/Injection.lagda.md:123-147
- The ambient answer at `ω` is delivered, so the mathematics of this site is not in question. Basis: src/L/InjChain.lagda.md:184-185
- `sq`. Basis: src/L/Ordinal/SquareLaw.lagda.md:685-687
- No literature under the name「square law」was found, and the fact itself is the square of an infinite cardinal. Basis: dev/literature/terms-2026-08.md:37

## WHAT IS DELIVERED ALREADY

**THE AMBIENT PAIRING AT `ω`**, `squareω` (`src/L/InjChain.lagda.md:184-185`).
**THE CODING PATTERN FOR ONE MAP**, `IdGraph`
(`agents/tasks/LJ-1-386/Probe386.agda:94-193`). **THE PRODUCT AND ITS BRIDGE**
(`agents/tasks/LJ-1-388/Probe388.agda:296` and `:299`). **THE DOOR**
(`agents/tasks/LJ-1-386/Probe386.agda:264-268`).

## WHAT IS MISSING

A code for any map other than the identity. The tree holds exactly one coded map
today.

## THE REASONING

**THIS TASK BUYS A NUMBER, AND THE NUMBER IS WHAT TWO ROUTES ARE BLOCKED ON.**

Every remaining route in this campaign owes a CODE for a map the tree already
holds ambiently. The coded route owes a code for a pairing
(`agents/tasks/LJ-1-386/Probe386.agda:288-290`). The positive side of the band
recursion owes a code for the collapse map that `InitialCore` spends its ambient
hypothesis on, at one line (`src/L/Ordinal/SquareLaw.lagda.md:876`). **Nobody
knows what one such code costs, because the tree has coded exactly one map and
that map is the identity.**

**SO MEASURE IT WHERE THE MATHEMATICS IS FREE.** At `ω` the ambient pairing is
delivered, the site is concrete, and no cardinal arithmetic is in question. What
is left is the coding work alone: the graph as an L-element, its placement below
the site bound, and the three satisfaction facts. **That is the number, and it is
the only honest basis for pricing the two blocked routes.**

**DO NOT GENERALISE THE NUMBER. Law C-42 binds this report** (`dev/LESSONS.md:3752`):
a measurement at `ω` measures `ω`. The report states the price at this site and
names what would change at a generic cardinal. It does not extrapolate.

**W2 (DD4).** The obligation is at ONE site by design, and that is a departure
from W2's write-once rule. **State the departure in the report and say which
parts of your construction are generic in the source and the target**, because
`[LJ-1.400]` will re-use them at a cardinal. A part that is accidentally specific
to `ω` is the finding this task must report.

**W3, THE WIDEST UNMEASURED TERM.** It is the PLACEMENT: `IdGraph` discharged
`⟨ fst G ∈ Lset β ⟩` at its own site (`agents/tasks/LJ-1-386/Probe386.agda:190-191`),
and a pairing graph is a bigger object than an identity graph. **The probe is
`graph-lands`: state the placement of your graph alone, run it FIRST, and report
its cost before you write a satisfaction fact.** If the placement fails, stop
there and report: the placement is the whole coding route's gate, and its failure
is worth more than a half-built code. ESTIMATE: about 150 code lines. BASIS:
`IdGraph` at about 100 lines for the identity
(`agents/tasks/LJ-1-386/Probe386.agda:94-193`) and `prodL` at 125 code lines for
one L-element with its membership reading
(`agents/tasks/LJ-1-388/lj-1.388-report.md:23`). **Both are comparables of
SHAPE. Do not fund anything against 150.**

## WHAT GO AND NO-GO EACH EARN

**A GO earns the campaign's first measured price for coding one ambient map**, and
it earns the end-to-end check that a code plus the bridge plus the door reaches
the ambient square law.

**A NO-GO earns the gate.** If the placement or a satisfaction fact cannot be
built for a pairing graph, then the coded route is blocked at the cheapest site it
has, and the campaign needs the owner. **That is a full return and the most
valuable one this task can give.**

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
  changed_files_any = ["agents/tasks/LJ-1-399/Probe399.agda"]
  changed_files_none = ["agents/tasks/LJ-1-399/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  error_class = "unsolved_meta"
  changed_files_any = ["agents/tasks/LJ-1-399/review-of-*.md"]

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

## YOUR ROLE (program-generated, do not edit)

**You write the Agda this brief names, and the probe it names (A21).** The mathematician specifies; you build it and make it typecheck. Your report is the other half of that channel, so write what the next brief will need.

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev/TASKS-archived.md, archive/dev/JOURNAL-archived.md, archive/dev/DECISIONS-archived.md, dev/ARCHIVE.md:
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 241.874)
- CANDIDATE dev/ARCHIVE.md  (score 195.036)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 174.151)
- CANDIDATE archive/dev/TASKS-archived.md  (score 146.061)
- CANDIDATE archive/src/2026-08-09-rud-route/Everything.lagda.md  (score 70.367)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 71.289)
- CANDIDATE dev/literature/devlin-II5.md  (score 60.551)
- CANDIDATE dev/literature/terms-2026-08.md  (score 57.770)
- CANDIDATE dev/literature/digest.md  (score 44.851)
- CANDIDATE dev/literature/geology.md  (score 38.800)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
