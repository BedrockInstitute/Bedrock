# LJ-1.414: is an ambient injection between two L-elements CODED in L?

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-414/Probe414.agda`.

    amb-to-coded :
        (x : S) (ox : IsOrd (fst x)) → ⟨ ω ∈ˢ fst x ⟩
      → (d : S) → ⟨ fst d ∈ˢ fst x ⟩ → (⟨ fst d ∈ˢ ω ⟩ → Empty.⊥)
      → ∥ ⟪ fst x ⟫ ↪ ⟪ fst d ⟫ ∥₁
      → ∥ Σ[ F ∈ S ] InjCode F x d ∥₁

**THIS IS THE CAMPAIGN'S LAST OPEN IMPLICATION AND THE TASK IS TO MEASURE IT,
NOT TO WIN IT.** It is `[LJ-1.413]`'s residue at a form that names no
`AmbCard`: with it, `IsCardinalL x → Empty.⊥` follows at once from the ambient
descent, because the code refutes the predicate at `d`
(`src/L/Cardinal.lagda.md:230-233`).

**READ THE LITERATURE BLOCK BEFORE YOU WRITE AGDA. W8 BINDS THIS TASK.** This
is a provability question and not an assembly. If the literature shows the
shape is an axiom, or a theorem with a hypothesis this tree does not meet,
**STOP AND REPORT. A literature NO-GO is a FULL return** and it is worth more
than a hole.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-414/Probe414.agda::amb-to-coded"]

## SCOPE (write)
- agents/tasks/LJ-1-414/Probe414.agda
- agents/tasks/LJ-1-414/lj-1.414-report.md
- agents/tasks/LJ-1-414/review-of-amb-to-coded.md

## PREMISES
- `InjCode` is four conjuncts about a set `F` that holds the pairs of a graph. Basis: src/L/Cardinal.lagda.md:223
- `IsCardinalL` is refuted by one code at one member, so a code at `d` is all the descent case needs. Basis: src/L/Cardinal.lagda.md:230
- The CODED to AMBIENT direction is delivered: `Small` reads a code back as an ambient injection. Basis: src/L/Coding/Injection.lagda.md:123
- The ambient arrow at the least cardinal is truncated where it is defined, and that is the step this implication would pay for. Basis: src/L/Cardinal.lagda.md:133
- `[LJ-1.394]` measured that nothing in the tree untruncates that ambient arrow. Basis: agents/tasks/LJ-1-394/lj-1.394-report.md:87
- The tree DOES carve a graph as an L-element when the map is definable: the inclusion. Basis: src/L/InjChain.lagda.md:575
- And it carves the composite of two graphs by separation. Basis: src/L/InjChain.lagda.md:338
- `[LJ-1.399]` measured wall 1: two hypotheses do not determine the members of an internal product. Basis: agents/tasks/LJ-1-399/lj-1.399-report.md:41
- `[LJ-1.399]` measured wall 2: the tree has no object-language addition and no multiplication, so a collapse cannot be written as a `Formula`. Basis: agents/tasks/LJ-1-399/lj-1.399-report.md:83
- `[LJ-1.400]` measured that the door packages a graph that the code does not supply. Basis: agents/tasks/LJ-1-400/lj-1.400-report.md:21
- `[LJ-1.408]` refuted the consumer-side cure, so this implication is what is left. Basis: agents/tasks/LJ-1-408/lj-1.408-report.md:16
- The literature index says what is digested and what is not. Basis: dev/literature/BIBLIOGRAPHY.md:1
- The condensation digest is the place an argument of this shape would live. Basis: dev/literature/devlin-II5.md:1

## WHAT IS DELIVERED ALREADY

**ONE DIRECTION OF THE BRIDGE.** `Small` (`src/L/Coding/Injection.lagda.md:123`)
turns a code into an ambient injection. Nothing turns an ambient injection into
a code.

**TWO CARVINGS, AND BOTH ARE OF DEFINABLE MAPS.** `InclGraph`
(`src/L/InjChain.lagda.md:575`) carves the graph of an inclusion and proves the
conjuncts. `K` (`src/L/InjChain.lagda.md:338`) carves a composite by
separation. Both maps have a `Formula`. An arbitrary ambient injection does
not.

**TWO MEASURED WALLS.** `[LJ-1.399]` at `:41` and `:83`, `[LJ-1.400]` at `:21`.
Both were about coding ONE named map. This task asks the general question that
those two instantiate.

## WHAT IS MISSING

**THE GENERAL QUESTION HAS NEVER BEEN ASKED.** `[LJ-1.399]` and `[LJ-1.400]`
each tried to code a NAMED map and each hit a wall of that map's own. Nobody
has stated the implication at the generality the recursion needs, and nobody
has separated its two halves: whether the GRAPH is an L-element, and whether
the four conjuncts follow once it is.

## THE REASONING

**SPLIT THE WALL IN TWO BEFORE YOU TOUCH THE OBLIGATION. THAT SPLIT IS THE
DELIVERABLE EVEN IF THE OBLIGATION STAYS A HOLE.**

- **HALF A. The graph exists as an L-element.** Some `G : S` holds exactly the
  pairs `pr u v` with `v` the value of the injection at `u`.
- **HALF B. The four conjuncts follow from that graph.** `InjCode G x d` from
  the two membership readings of `G`.

**HALF B IS W3 AND YOU BUILD IT FIRST.** See below. If half B is GREEN, then
the campaign's whole remaining bill is HALF A, and it is one type. **Write that
type down in your report.** That single line is what `[LJ-2.5]` needs and it is
worth more than anything else this task can return.

**THEN THE OBLIGATION.** Attempt `amb-to-coded`. If half A has no producer,
leave the obligation as a hole and write the obstruction in
`review-of-amb-to-coded.md`. **Do not invent a hypothesis to close it.** Do not
add an axiom, a postulate or a module parameter that asserts half A: a term
that assumes what the task measures returns nothing.

**D-10 FIRST, AND ANSWER IT IN WRITING BEFORE THE AGDA.** Price the TRUTH of
this target before its proof. The injection is a function on the fibre types of
two L-elements, and nothing in its type says it is constructible. **Say
whether the statement can be TRUE at this generality, and give the `file:line`
your answer rests on.** Three answers are admissible and you must pick one:

1. TRUE and provable here, and then build it.
2. TRUE under a condition the tree can meet, and then NAME the condition as a
   type and say which chapter would supply it.
3. NOT DECIDABLE in this tree, and then say so with the reason. **This is a
   full return**, and it says the internalization route cannot untruncate the
   ambient square law at a non-initial ordinal.

**W2 (DD4).** The statement is generic in `x` and `d`. Name no cardinal, no
site and no numeral except `ω`. A refutation, if you find one, names ONE site,
and C-42 then binds you to the sweep.

**W3, THE WIDEST UNMEASURED TERM.** It is HALF B.

    code-from-graph :
        (x d : S) (G : S)
      → (the two membership readings of `G` as bare hypotheses,
         in the shape `InclGraph` states them)
      → InjCode G x d

**State it ALONE, run it, and report its code lines and which of the four
conjuncts cost anything.** ESTIMATE: about 45 code lines. BASIS: `InclGraph`
proves the same four conjuncts for the inclusion at
`src/L/InjChain.lagda.md:575-607`, and `[LJ-1.409]`'s `TrimCode` closed the
same four from a carved subset at 23 code lines for one conjunct and about 90
for the block (`agents/tasks/LJ-1-409/lj-1.409-report.md:36-49`).
**Comparables of SHAPE, not of size, and nothing may be funded against them.**

**THE C-42 SWEEP IS REQUIRED, WHATEVER THE OUTCOME.** Count the sites in `src/`
that carve the graph of an ambient function as an L-element, and for each one
say whether the map has a `Formula`. Report the COUNT before any opinion about
how far the wall extends. Two are named above; nobody has counted the rest.

## WHAT GO AND NO-GO EACH EARN

**A GO CLOSES THE CAMPAIGN'S LAST IMPLICATION.** With `[LJ-1.411]` to
`[LJ-1.413]`, the consumer's module parameter is then delivered as data and the
counting chapter opens.

**A NO-GO EARNS THE BILL, STATED ONCE AND FOR ALL, AND THAT IS WHAT `[LJ-2.5]`
ASKS FOR.** Name half A as a type, name the two walls it inherits at
`file:line`, and say whether the tree could pay it with a chapter or whether it
cannot be paid on the Def tower at all. **A stated NO-GO is a full return**,
and here it is the more likely one.

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
  changed_files_any = ["agents/tasks/LJ-1-414/Probe414.agda"]
  changed_files_none = ["agents/tasks/LJ-1-414/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  error_class = "unsolved_meta"
  changed_files_any = ["agents/tasks/LJ-1-414/review-of-*.md"]

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
- CANDIDATE archive/src/2026-08-09-rud-route/L/Condensation.lagda.md
- CANDIDATE archive/src/2026-08-09-rud-route/L/Coding
- CANDIDATE archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md
- CANDIDATE archive/dev/TASKS-archived.md
- CANDIDATE archive/dev/JOURNAL-archived.md
- CANDIDATE archive/dev/LJ-dispatch-index.md
- CANDIDATE dev/ARCHIVE.md

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md
- CANDIDATE dev/literature/j-hierarchy.md
- CANDIDATE dev/literature/truncation-and-selection.md
- CANDIDATE dev/literature/digest.md
- CANDIDATE dev/literature/BIBLIOGRAPHY.md

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
