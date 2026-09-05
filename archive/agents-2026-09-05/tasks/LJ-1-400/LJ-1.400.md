# LJ-1.400: the coded square law at an L-cardinal, and it is the last obligation

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-400/Probe400.agda`, at a GENERIC L-cardinal,
and state the residue as a second.

    card-owes : Type (ℓ-suc ℓ)

    card-pair-code :
        card-owes
      → (κ : S) → IsOrd (fst κ) → IsCardinalL κ → ⟨ ω ∈ fst κ ⟩
      → ∥ Σ[ A ∈ Mem (Lset (SiteBound.β (prodL κ κ))) ]
            InjCode (SiteBound.up (prodL κ κ) A) (prodL κ κ) κ ∥₁

**READ THE INJECTED LITERATURE BLOCK BEFORE YOU WRITE ONE LINE OF AGDA. Clause
W8 binds this task**, because the target is a provability question. **THE
MATHEMATICS IS NOT DIGESTED IN THIS REPOSITORY**: no source under the name
「square law」was found and the fact itself is that an infinite cardinal squared
is itself (`dev/literature/terms-2026-08.md:37`), while the digest names the
Gödel pairing only inside a HYPOTHESIS of the J-hierarchy results
(`dev/literature/j-hierarchy.md:111`). **So this task carries a literature step of
its own, and it comes first.** If the literature shows the internal form needs a
condition this tree does not meet, that is a full return and you stop, per W8.

`card-owes` is a type YOU write. It names what the code still needs when your
construction stops. **A stated residue with a price is this task's expected
outcome, and a green `card-pair-code` with `card-owes` empty would close the
campaign's coded route.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-400/Probe400.agda::card-owes",
               "agents/tasks/LJ-1-400/Probe400.agda::card-pair-code"]

## SCOPE (write)
- agents/tasks/LJ-1-400/Probe400.agda
- agents/tasks/LJ-1-400/lj-1.400-report.md

## PREMISES
- This is the one unpaid conjunct of the coded route, stated at the band ordinal by `[LJ-1.386]`. Basis: agents/tasks/LJ-1-386/Probe386.agda:288-290
- `[LJ-1.388]` calls it the cardinal arithmetic and says it measured nothing about it. Basis: agents/tasks/LJ-1-388/lj-1.388-report.md:236-241
- `prodL` and `prod-bridge` are delivered at generic arguments. Basis: agents/tasks/LJ-1-388/Probe388.agda:296
- The door consumes exactly this shape and returns an ambient injection as data. Basis: agents/tasks/LJ-1-386/Probe386.agda:264-268
- `leg1-gives-sq` closes the route from the two conjuncts, untruncated. Basis: agents/tasks/LJ-1-386/Probe386.agda:294-295
- The tree holds the ambient Gödel order on pairs of ordinal indices, and its collapse. Basis: src/L/Ordinal/SquareLaw.lagda.md:308-315
- It holds the collapse at a fixed ordinal, `god`, with the well-foundedness the recursion needs. Basis: src/L/Ordinal/SquareLaw.lagda.md:754-755
- `via-col-square` is the delivered AMBIENT theorem the collapse proves, under `Init`. Basis: src/L/Ordinal/SquareLaw.lagda.md:960-961
- `Init`'s fourth conjunct refutes an AMBIENT injection, and the chapter spends it at exactly ONE line. Basis: src/L/Ordinal/SquareLaw.lagda.md:876
- `IsCardinalL` refutes a CODED injection, which is the opposite direction. Basis: src/L/Cardinal.lagda.md:230-233
- `InjCode`'s four conjuncts. Basis: src/L/Cardinal.lagda.md:223-228
- The literature names the Gödel pairing only as a hypothesis of a J-hierarchy result. Basis: dev/literature/j-hierarchy.md:111
- No literature was found under the name of the fact. Basis: dev/literature/terms-2026-08.md:37
- The tree holds exactly one coded map, the identity. Basis: agents/tasks/LJ-1-386/Probe386.agda:94-193

## WHAT IS DELIVERED ALREADY

**THE AMBIENT THEOREM.** `via-col-square` proves the square law from `Init`
(`src/L/Ordinal/SquareLaw.lagda.md:960-961`), and the whole Gödel collapse behind
it is built and green (`:308-315`, `:754-755`, `:931-936`). **The mathematics of
the square law is IN THIS TREE. What is not in this tree is that mathematics in
CODED form.**

**THE TWO ENDS OF THE ROUTE.** `prodL` with its bridge
(`agents/tasks/LJ-1-388/Probe388.agda:296`), and the door
(`agents/tasks/LJ-1-386/Probe386.agda:264-268`).

## WHAT IS MISSING

The middle: a code, at an L-cardinal, for an injection out of the internal
square.

## THE REASONING

**READ THE AMBIENT PROOF FIRST AND DECIDE WHICH OF TWO ROUTES IS CHEAPER. SAY
WHICH YOU TOOK AND WHY.**

**ROUTE A, CODE THE COLLAPSE.** The ambient proof builds the pairing from the
Gödel order's collapse (`src/L/Ordinal/SquareLaw.lagda.md:944-954`), under `Init`.
`Init`'s fourth conjunct is AMBIENT, and it is spent at exactly one line, on one
constructed map (`src/L/Ordinal/SquareLaw.lagda.md:876`). So route A is: code the
collapse, then discharge the narrowed clause from `IsCardinalL`. **Its price is
the price of coding a map defined by well-founded recursion, and nobody has
measured that.**

**ROUTE B, BUILD THE CODE DIRECTLY.** Build the graph of a pairing of `κ` as an
L-element and prove `InjCode`'s four conjuncts of it, with the cardinal
arithmetic done inside the object language.

**`[LJ-1.399]` MEASURES THE UNIT PRICE OF BOTH ROUTES**, by coding one delivered
map at `ω`. **Read its report before you price anything here.** If it has not
landed, say so and price against `IdGraph` instead
(`agents/tasks/LJ-1-386/Probe386.agda:94-193`).

**WHAT MAKES THIS THE LAST OBLIGATION.** With this conjunct paid, `Leg1` is
complete at a cardinal, `leg1-gives-sq` gives the ambient square law as DATA
there (`agents/tasks/LJ-1-386/Probe386.agda:294-295`), and `[LJ-1.398]`'s
recursion carries it to every band ordinal. **Say in the report which of those two
statements you checked and which you took on report.**

**W2 (DD4).** Write the construction generic in `κ`. If a step needs a property
that only some cardinals have, state that property as a hypothesis of
`card-owes` and never name a site. Answer W2 in the report.

**W3, THE WIDEST UNMEASURED TERM. IT IS THE OBJECT-LANGUAGE STATEMENT OF THE
COLLAPSE.** `[LJ-1.388]` measured that the two-replacement route needs two
object-language artifacts the tree does not hold
(`agents/tasks/LJ-1-388/lj-1.388-report.md:14-19`), and the collapse needs at
least as much. **The probe is `collapse-states`: write the object-language
statement you would need, alone, with no proof, and report whether the tree holds
a formula for it.** Run that BEFORE any construction. ESTIMATE: about 300 code
lines, and the estimate is weak. BASIS: `IdGraph` at about 100 lines for the
identity, `prodL` at 125 code lines for one L-element
(`agents/tasks/LJ-1-388/lj-1.388-report.md:23`), and the ambient collapse at
about 250 lines in the chapter (`src/L/Ordinal/SquareLaw.lagda.md:703-956`).
**Nothing may be funded against 300. The number exists so a NO-GO can be
compared with it.**

## WHAT GO AND NO-GO EACH EARN

**A GO closes the coded route and, with `[LJ-1.398]`, the module parameter that
blocks the whole GCH wing.** No other open task in this campaign can do that.

**A NO-GO IS WORTH AS MUCH, AND IT GOES TO `[LJ-2.5]`.** If coding one definable
ambient map needs the rudimentary tower, then the J tower is on the critical path
for GCH, and that is the first MEASURED warrant for the candidate architecture
(clause W1, `dev/PLAN.md` section 11's `[LJ-2.5]` row). **State that reading
explicitly in the report if the evidence supports it, and state that it does not
if it does not.**

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
  changed_files_any = ["agents/tasks/LJ-1-400/Probe400.agda"]
  changed_files_none = ["agents/tasks/LJ-1-400/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  error_class = "unsolved_meta"
  changed_files_any = ["agents/tasks/LJ-1-400/review-of-*.md"]

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
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 234.410)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 194.714)
- CANDIDATE dev/ARCHIVE.md  (score 188.117)
- CANDIDATE archive/dev/TASKS-archived.md  (score 159.655)
- CANDIDATE archive/src/2026-08-09-rud-route/Everything.lagda.md  (score 72.055)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 62.032)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 52.090)
- CANDIDATE dev/literature/digest.md  (score 51.013)
- CANDIDATE dev/literature/geology.md  (score 47.726)
- CANDIDATE dev/literature/terms-2026-08.md  (score 38.188)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
