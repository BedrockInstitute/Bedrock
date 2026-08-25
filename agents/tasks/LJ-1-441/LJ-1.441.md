# LJ-1.441: the ambient-to-coded crossing, asked at its ONE use site

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-441/Probe441.agda`:

    amb-to-coded-at-least :
        (a : S) (oa : IsOrd (fst a)) → ⟨ ω ∈ˢ fst a ⟩
      → ⟨ fst (κL a oa) ∈ˢ fst a ⟩
      → (⟨ fst (κL a oa) ∈ˢ ω ⟩ → Empty.⊥)
      → ∥ Σ[ F ∈ S ] InjCode F a (κL a oa) ∥₁

where `κL` is the four-projection seal of `LeastCardInjL` that `[LJ-1.433]`
builds at `agents/tasks/LJ-1-433/Probe433.agda:79-90`.

**THERE IS NO AMBIENT-ARROW HYPOTHESIS IN THAT TELESCOPE, AND THAT IS THE
WHOLE POINT.** The arrow is `κ-injL a oa`, which the seal already supplies
(`agents/tasks/LJ-1-433/Probe433.agda:89-90`). You are not asked to code an
arbitrary ambient injection. You are asked to code the ONE injection this
tree itself selected.

Land nothing in `src/`.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-441/Probe441.agda::amb-to-coded-at-least"]

## SCOPE (write)
- agents/tasks/LJ-1-441/Probe441.agda
- agents/tasks/LJ-1-441/lj-1.441-report.md
- agents/tasks/LJ-1-441/review-of-amb-to-coded-at-least.md
- agents/tasks/LJ-1-441/runs/

## PREMISES

1. `[LJ-1.420]` assembles the whole ambient chain into `stage-card-upper` under exactly ONE named hypothesis, `amb-to-coded`. Basis: agents/tasks/LJ-1-420/Probe420.agda:97
2. That hypothesis is `[LJ-1.414]`'s type, and `[LJ-1.414]` left it a hole because HALF A has no producer at a GENERIC pair. Basis: agents/tasks/LJ-1-414/Probe414.agda:134
3. HALF B is green: the four conjuncts of `InjCode` follow from the two membership readings. Basis: agents/tasks/LJ-1-414/Probe414.agda:115
4. The block is HALF A, `Σ[ G ∈ S ] GraphOf x d f G`, at an arbitrary ambient injection. Basis: agents/tasks/LJ-1-414/Probe414.agda:65
5. The chain spends the hypothesis at ONE pair only: `x := a` and `d := κL a oa`, with the arrow `κ-injL`. Basis: agents/tasks/LJ-1-413/lj-1.413-report.md:87
6. At that pair the tree carries a minimality the generic statement does not: `κ-min-at`. Basis: src/L/Cardinal.lagda.md:140
7. The selection's own predicate is a truncated AMBIENT injection, so its witness is not coded by construction. Basis: src/L/Cardinal.lagda.md:133
8. A measured cure does not transfer by analogy; re-measure at its own site. C-42 governs this task in BOTH directions. Basis: dev/LESSONS.md:3752
9. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
10. The architecture is a CANDIDATE and only a measurement settles it. Basis: dev/pod/screen.toml:10
11. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THE AMBIENT ROUTE IS COMPLETE EXCEPT FOR THIS ONE STATEMENT.**
`[LJ-1.420]` is GO. Its `chain-upper` (`agents/tasks/LJ-1-420/Probe420.agda:97-99`)
IS `L.StageCardinal`'s own `stage-card-upper` at every band ordinal, and its
telescope holds exactly one hypothesis: `amb-to-coded` at `[LJ-1.414]`'s
delivered type (`agents/tasks/LJ-1-420/Probe420.agda:75-96`). Read
`agents/tasks/LJ-1-420/lj-1.420-report.md` for the verdict line before you
believe that sentence.

`[LJ-1.414]` measured the hypothesis at full generality and left it a hole.
HALF B is green (`Probe414.agda:115-128`). HALF A has no producer
(`agents/tasks/LJ-1-414/review-of-amb-to-coded.md`).

## WHAT IS MISSING

**NOBODY HAS ASKED THE QUESTION AT THE SITE THE CHAIN USES.** `[LJ-1.414]`
asked it with the arrow as a HYPOTHESIS at a generic `d`. The chain never
spends it there. It spends it at `d := κL a oa`, where the arrow is not
arbitrary: it is `fst (snd least)` out of the chapter's own `leastOf`
(`src/L/Cardinal.lagda.md:133-134`), and the ordinal is the LEAST member of
`sucV (fst a)` admitting any ambient injection at all.

C-42 cuts both ways and this brief states both halves. `[LJ-1.414]`'s NO-GO
at generality does NOT measure this site. Equally, a GO here does NOT
inhabit `[LJ-1.414]`'s type, and your report must say so.

## THE REASONING

**D-10, BEFORE ANY AGDA.** Price the truth of the target at this generality
before you price its proof.

1. Open `agents/tasks/LJ-1-420/lj-1.420-report.md` and quote its VERDICT line
   at `file:line`. Open `agents/tasks/LJ-1-414/lj-1.414-report.md` and quote
   its VERDICT line at `file:line`. `[LJ-1.414]` is a NO-GO on the name
   `amb-to-coded`, so you may NOT write `[LJ-1.414]`'s type into this file as
   an inhabited hypothesis. You may quote it as the type this task does NOT
   inhabit.
2. Write down, at `file:line`, what the selection gives you at `κL a oa` that
   a generic `d` does not. There are exactly two candidates in the chapter and
   you must name both: `κ-min-at` (`src/L/Cardinal.lagda.md:140-141`) and
   `κ∈sα` (`src/L/Cardinal.lagda.md:129-130`).
3. Say in one sentence whether either of them puts a `Formula` anywhere.
   `[LJ-1.414]`'s D-10 says the ambient injection type carries none
   (`agents/tasks/LJ-1-414/review-of-amb-to-coded.md`, D-10 section). **If
   your answer is that neither does and no third device exists, that is a
   NO-GO and you write it after W3, not before.** D-10 prices the target; it
   does not close the task.

**STEP ONE, W3 FIRST.** See the W3 section. Run it ALONE, with the obligation
omitted from the file, before you attempt the obligation.

**STEP TWO, THE OBLIGATION.** Attempt `amb-to-coded-at-least`. Two routes are
open and you choose by what W3 measured:

- **Route 1, through the graph.** `PT.rec` on `κ-injL a oa` into the truncated
  goal, then HALF A at the opened arrow, then `[LJ-1.414]`'s green HALF B
  (`Probe414.agda:115-128`) to reach `InjCode`. The goal is a truncation, so
  `PT.rec` into it is legal with `squash₁`.
- **Route 2, through minimality.** Ask whether `κ-min-at` constrains the
  selected ordinal enough to name the graph. State what you tried.

**DO NOT INVENT A HYPOTHESIS TO CLOSE IT.** Adding a module hypothesis whose
type is the statement under proof, or whose type a predecessor report named
FALSE, is the exact shape the independent audit measured twice
(`dev/pod/audit-2026-08-20.md:34` and `:52`). If the obligation does not close,
leave it a HOLE and write the obstruction.

**A NO-GO IS A FULL RETURN HERE AND IT IS WORTH AS MUCH AS A GO.** Write
`agents/tasks/LJ-1-441/review-of-amb-to-coded-at-least.md` and state, AS A
TYPE, the one declaration that would close HALF A at this site. Say plainly
whether the obstruction is the same one `[LJ-1.414]` met or a different one.
That answer is what `[LJ-2.5]` needs, because it decides whether the ambient
route is dead at generality only or dead at its own site.

**W2 (DD4).** Write the mathematics once at a generic carrier. The module is
generic in `ℓ` and in `a`. Name no band, no numeral except `ω`, and no site.

**C-42.** In a section `## WHAT THIS DOES NOT MEASURE`, say plainly that a GO
here does not inhabit `[LJ-1.414]`'s generic type, and that a NO-GO here says
nothing about the TRUNCATED route, whose supply is `[LJ-1.437]` and whose
consumer is `[LJ-1.434]`.

**NEVER COMMIT AND NEVER PUSH.** Leave the working tree exactly as your report
describes it.

ESTIMATE for the Agda: about 130 code lines. BASIS: a delivered comparable of
SHAPE, `agents/tasks/LJ-1-433/Probe433.agda` at 119 non-blank non-comment
lines, which rebuilds the same four-projection `κL` seal and adds one term
about the selected arrow. Comparables are of SHAPE and never of size, and
nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is HALF A at the SELECTED arrow, and it is unmeasured because every
measurement of HALF A in this tree was taken at a hypothesised arrow:

    half-a-at-least :
        (a : S) (oa : IsOrd (fst a)) → ⟨ fst (κL a oa) ∈ˢ fst a ⟩
      → ∥ Σ[ f ∈ (⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫) ]
            (Σ[ G ∈ S ] GraphOf a (κL a oa) f G) ∥₁

with `GraphOf` copied from `agents/tasks/LJ-1-414/Probe414.agda:56-63`, not
imported. **Write this term, typecheck it ALONE with the obligation omitted
from the file, and report its median wall time and peak RSS over three forced
rechecks at the pane's caliber.** A failure here kills the task in one probe
and the NO-GO is then cheap and complete.

ESTIMATE for W3: about 45 code lines. BASIS: `agents/tasks/LJ-1-414/Probe414.agda:56-66`,
the same two membership readings, delivered.

## WHAT GO AND NO-GO EACH EARN

**A GO ENDS THE AMBIENT ROUTE'S LAST OPEN STATEMENT.** With `[LJ-1.420]`'s
`chain-upper`, it puts `stage-card-upper` at every band ordinal under NO
hypothesis at all. Say so in the report, and say it as a composition, naming
`[LJ-1.420]`'s term at `file:line`. Do not claim a trophy: the trophy case is
`src/Landmarks.lagda.md` and this task writes nothing in `src/`.

**A NO-GO NAMES, AS A TYPE, THE ONE DECLARATION HALF A WOULD NEED AT THE
SELECTED ARROW**, and says whether it is `[LJ-1.414]`'s obstruction or a new
one. That answer settles whether `[LJ-2.5]` has one open statement or two.

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
  changed_files_any = ["agents/tasks/LJ-1-441/Probe441.agda"]
  changed_files_none = ["agents/tasks/LJ-1-441/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-441/review-of-*.md"]

[[branch]]
id = "heap-wall-escalate"
priority = 30
action = "escalate"
head_slot = "coder_adversarial"

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

**THE RATIO BAR IS LIVE AND IT IS 0.0123 SECONDS PER IN-FENCE LINE.** A green return at or above that rate is ESCALATED to a critic by row `sys-dd24-ratio-bar`, which is DD24 restored by amendment A10. The divisor is fact 7, the in-fence line count of THIS task's write scope, counted the ledger's way: non-blank lines inside ` ```agda ` fences. **A raw `.agda` probe carries no fence and counts 0**, so the bar cannot fire on a probe and it binds the moment you write a `.lagda.md` master under `src/`. Design for it rather than discovering it: the number comes from `dev/pod/table.toml` at brief build, and its measured basis is in `dev/ledger.toml [ratio]`.

## LAWS (program-generated, do not edit)

MANDATORY for kind `recon` (read-only: an audit, a design pass, a history dig. It writes a report and nothing else. The sweep C-42 demands is a recon action, so this is that law's home bundle.):

- **D-10. Price the truth of a recorded residue before pricing its proof**
  **Rule:** A residue recorded under the wall protocol names a TARGET, and a target can be false; before dispatching a discharge batch, spend the five minutes checking the target's truth at the intended generality (a Tarskian or cardinality obstruction is the usual killer), and record the corrected target beside the original.
  Full entry: dev/LESSONS.md:1375
- **C-22. A dispatched agent writes its deliverable incrementally, never at the end**
  **Rule:** When an agent's deliverable is a file, the brief must require it WRITTEN EARLY as a skeleton and filled incrementally, saving after each answer lands. An agent that researches for its whole budget and leaves the writing to the end returns nothing when the budget runs out, and its research dies with it. A partial dossier is a real deliverable; an unwritten perfect one is not.
  Full entry: dev/LESSONS.md:2297
- **P-l. A statement may be ABOUT a concrete stage without dragging that stage's PRESENTATION into its type**
  **The law.** Being about a concrete position is not what costs. Naming a transparent construction in a statement's TYPE is. If the tower's stage values are `opaque` upstream, a theorem may quantify over, hypothesize about and conclude at `Sset ω` freely, because the stage is an ATOM to the elaborator and nothing unfolds. If instead the type mentions a transparent presentation, such as `⟪ sucV (...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2357
- **D-26. A well-founded key on a tower needs generation data, or it needs syntax**
  **Rule:** When a route must well-order a cumulative tower's stage, ask first what the stage's members CARRY. A stage built as the values of finitely many total operations carries its own generation data, so a well-founded key exists with NO syntax at all: the operation index, then the arguments, ordered recursively. A stage built as a definable power carries nothing: its members are sets, not c...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:1735
- **C-42. A refutation measures the site it names, and it never measures how far that site extends**
  **Rule:** A refutation is a measurement of ONE site. It says the statement there is false. **It says nothing about how many other sites carry the same false shape.** So when a refutation lands, the next action is not the cure. **It is the sweep: search the tree for the shape, and report the COUNT before you price the cure.** A cure funded against the named site is priced against a number nobody...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:3752

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev, archive/scripts, dev/ARCHIVE.md:
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 161.249)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 140.062)
- CANDIDATE dev/ARCHIVE.md  (score 125.263)
- CANDIDATE archive/dev/JOURNAL.md  (score 124.009)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 94.814)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 48.598)
- CANDIDATE dev/literature/digest.md  (score 40.369)
- CANDIDATE dev/literature/devlin-II5.md  (score 38.549)
- CANDIDATE dev/literature/terms-2026-08.md  (score 29.418)
- CANDIDATE dev/literature/rudimentary-functions.md  (score 25.053)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
