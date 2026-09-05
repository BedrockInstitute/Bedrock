# LJ-1.413: the square law as DATA at every band ordinal, with ONE residue

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-413/Probe413.agda`, at a GENERIC band
`α₀` with its ordinal certificate as module parameters.

    sq-data :
        (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → sq δ

**THERE IS NO `∥ ∥₁` IN THE CONCLUSION. THAT IS THE WHOLE TASK.** The type
above is the consumer's module parameter, verbatim
(`src/L/StageCardinal.lagda.md:17-19`). `[LJ-1.407]` delivered the same
recursion with `∥ sq δ ∥₁` as its motive and no residue, and `[LJ-1.408]`
refuted the one way of feeding that truncated form to the consumer
(`agents/tasks/LJ-1-408/lj-1.408-report.md:16`).

**THREE MODULE HYPOTHESES, EACH AT A TYPE THAT IS ALREADY WRITTEN DOWN.**

1. `init-at-kappa`, at `[LJ-1.406]`'s type
   (`agents/tasks/LJ-1-406/Probe406.agda:180`), the way `[LJ-1.407]` took it
   (`agents/tasks/LJ-1-407/Probe407.agda:203-209`).
2. `coded-descent`, at `[LJ-1.412]`'s type.
3. **THE RESIDUE**, and it is the point of the task:

       amb-to-coded :
           (x : S) (ox : IsOrd (fst x)) → ⟨ ω ∈ˢ fst x ⟩
         → (d : S) → ⟨ fst d ∈ˢ fst x ⟩ → (⟨ fst d ∈ˢ ω ⟩ → Empty.⊥)
         → ∥ ⟪ fst x ⟫ ↪ ⟪ fst d ⟫ ∥₁
         → (IsCardinalL x → Empty.⊥)

Do not import `Probe406`, `Probe407` or `Probe412`. Rebuild only what the four
cases spend.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-413/Probe413.agda::sq-data"]

## SCOPE (write)
- agents/tasks/LJ-1-413/Probe413.agda
- agents/tasks/LJ-1-413/lj-1.413-report.md
- agents/tasks/LJ-1-413/review-of-sq-data.md

## PREMISES
- The consumer takes the pairing as a module parameter, so it must be DATA before the module opens. Basis: src/L/StageCardinal.lagda.md:17
- `[LJ-1.408]` refuted the one way of moving that data inside the consumer's truncation. Basis: agents/tasks/LJ-1-408/lj-1.408-report.md:16
- `via-col-square` returns `sq α` as DATA from `Init α`, and it is delivered and sealed. Basis: src/L/Ordinal/SquareLaw.lagda.md:960
- `Init` is four conjuncts, every one a proposition, so it can be built from truncated inputs. Basis: src/L/Ordinal/SquareLaw.lagda.md:692
- `sq` is the pairing and its injectivity, a Sigma, and it is NOT a proposition. Basis: src/L/Ordinal/SquareLaw.lagda.md:685
- `[LJ-1.406]` built `Init` at the ambient least cardinal from truncated inputs, green. Basis: agents/tasks/LJ-1-406/Probe406.agda:180
- `[LJ-1.407]` ran the same four-case recursion with a truncated motive and left NO residue. Basis: agents/tasks/LJ-1-407/Probe407.agda:217
- `kappa-decides` is the split this recursion takes, and it is already written. Basis: agents/tasks/LJ-1-407/Probe407.agda:140
- `descent-core` carries a pairing down an ambient arrow, at data level. Basis: agents/tasks/LJ-1-390/Probe390.agda:135
- `squareω` is the delivered pairing at `ω`, as data. Basis: src/L/InjChain.lagda.md:184
- `[LJ-1.404]` REFUTED the `⟨ ω ∈ κ ⟩` spelling at the selected cardinal, so the residue must use the `∈ ω → ⊥` spelling. Basis: agents/tasks/LJ-1-404/lj-1.404-report.md:18
- The ambient injection into the ambient least cardinal is truncated at its definition site, and that is the only truncated step left. Basis: src/L/Cardinal.lagda.md:133
- `[LJ-1.394]` measured that nothing in the tree untruncates that ambient arrow. Basis: agents/tasks/LJ-1-394/lj-1.394-report.md:87
- The consumer's shape check that `[LJ-1.407]` wrote is the model for this task's. Basis: agents/tasks/LJ-1-407/Probe407.agda:273

## WHAT IS DELIVERED ALREADY

**THREE OF THE FOUR CASES.** `[LJ-1.407]` closed all four with a truncated
motive (`agents/tasks/LJ-1-407/Probe407.agda:217-260`). Three of them never
used the truncation:

- `x ∈ ω` is refuted by the infinitude hypothesis.
- `x ≡ ω` is `squareω`, transported. DATA (`src/L/InjChain.lagda.md:184`).
- `ω ∈ x` with `fst κ ≡ x` is `init-at-kappa` then `via-col-square`. DATA,
  because `Init` is a proposition and `via-col-square` returns the Sigma
  (`src/L/Ordinal/SquareLaw.lagda.md:960`).

**THE FOURTH CASE IS THE ONLY ONE THAT SPENT THE TRUNCATION.** `[LJ-1.407]`
closed it with `PT.map2` over the truncated ambient arrow `κ-inj`
(`src/L/Cardinal.lagda.md:133`). With a data motive there is no `PT.map2`.

**THE DESCENT AS DATA EXISTS ON THE CODED SIDE.** `[LJ-1.412]` returns the
target, its membership, its infiniteness and the arrow, all as data.

## WHAT IS MISSING

**ONE IMPLICATION, AND THIS TASK NAMES IT AS A TYPE.** The coded descent runs
from `IsCardinalL x → Empty.⊥`. The ambient split hands case four an ambient
arrow instead. `amb-to-coded` is the bridge and nothing in the tree builds it.
**This task does not attempt it. `[LJ-1.414]` measures it.**

## THE REASONING

**THE SPLIT IS THE AMBIENT ONE, NOT THE INTERNAL ONE, AND THAT CHOICE BUYS A
WHOLE CASE.** Under the ambient split, case three is `[LJ-1.406]`, which is
green today. Under an `IsCardinalL` split, case three would need `Init` from
the internal cardinal predicate, which nothing delivers. **One residue, not
two.**

**THE FOUR CASES.**

1. `x ∈ ω`: refuted by the hypothesis, as `[LJ-1.407]` does at `:224`.
2. `x ≡ ω`: `squareω`, transported along the equality. No truncation.
3. `ω ∈ x` and `fst κ ≡ x`: `init-at-kappa` gives `Init (fst κ)`,
   `via-col-square` gives `sq (fst κ)` as DATA, transport along the equality.
   **Do not wrap it. `[LJ-1.407]` wrapped it only because its motive was
   truncated.**
4. `ω ∈ x` and `fst κ ∈ x`: `amb-to-coded` on `κ-inj` gives
   `IsCardinalL x → Empty.⊥`; `coded-descent` gives `d`, its membership, its
   infiniteness and the arrow, all as data; the recursion's own `IH` at `d`
   gives `sq d`; `descent-core` gives `sq x`.

**THE BAND MEMBERSHIP AT THE DESCENT TARGET.** `d ∈ x` and `x ∈ sucV α₀` give
`d ∈ sucV α₀` by the transitivity of an ordinal, which `κ-min-at` already
spends in one line (`src/L/Cardinal.lagda.md:145`). Rebuild it, and do not
carry the band into `[LJ-1.412]`'s telescope.

**THE INFINITENESS AT THE DESCENT TARGET COMES FROM `[LJ-1.412]`, NOT FROM A
HYPOTHESIS.** It arrives in the consumer's spelling, `⟨ fst d ∈ˢ ω ⟩ → ⊥`,
which is the spelling the IH wants. `[LJ-1.404]` refuted the other spelling
(`agents/tasks/LJ-1-404/lj-1.404-report.md:18`).

**W2 (DD4).** `sq-data` is generic in the band. Name no cardinal and no numeral
except `ω`. The residue is generic in `x` and `d`.

**W3, THE WIDEST UNMEASURED TERM.** It is CASE FOUR AT DATA LEVEL, because
every delivered form of it runs under a truncation.

    descent-data : (x d : S) → ⟨ fst d ∈ˢ fst x ⟩
                 → ⟪ fst x ⟫ ↪ ⟪ fst d ⟫ → sq (fst d) → sq (fst x)

**State it ALONE with three bare hypotheses, run it, and report its code lines
before you write the recursion.** ESTIMATE: about 10 code lines. BASIS:
`[LJ-1.390]`'s `descent-gives-sq` is the same composition and it is green at
`agents/tasks/LJ-1-390/Probe390.agda:135-142`. ESTIMATE for the whole
obligation: about 75 code lines. BASIS: `[LJ-1.407]`'s `step` and `sq-trunc`
occupy `agents/tasks/LJ-1-407/Probe407.agda:217-265`, and this task drops the
truncation plumbing of case four and adds the residue's telescope.
**Comparables of SHAPE, not of size, and nothing may be funded against them.**

**MEASURE THE MOTIVE, AND REPORT IT.** `[LJ-1.407]`'s motive was a proposition
and this one is a Sigma. `∈-induction` does not care, but the elaborator may:
LESSONS P-l and R-40 are in your laws block. **Report the wall time of the
recursion against `[LJ-1.407]`'s median of 1.77 s
(`agents/tasks/LJ-1-407/lj-1.407-report.md:19`), and say whether the data
motive cost anything.**

**CLOSE WITH THE CONSUMER CHECK.** Restate the consumer's parameter type
verbatim as `ConsumerShape`, with NO `∥ ∥₁`, and discharge it with `sq-data`,
the way `[LJ-1.407]` discharged its truncated form
(`agents/tasks/LJ-1-407/Probe407.agda:273-280`). **A term that does not plug in
has not finished.**

**D-10.** The residue can be false, and pricing its truth is `[LJ-1.414]`'s
task and not yours. **Do not try to prove it here and do not weaken it to
something you can prove.** State it, use it, and report the exact type you
used.

## WHAT GO AND NO-GO EACH EARN

**A GO REDUCES THE WHOLE CAMPAIGN TO ONE IMPLICATION.** The consumer's module
parameter is then delivered, up to `amb-to-coded`, and `[LJ-1.414]` measures
that one type. Say in your report what is left, as a type, and nothing else.

**A NO-GO EARNS THE CASE THAT WILL NOT CLOSE AT DATA LEVEL, AT `file:line`.**
If case two or case three needs a truncation that `[LJ-1.407]` hid, name it.
**That would be worth more than the GO**, because it would say the data form
is unreachable even with the residue granted. **A stated NO-GO is a full
return.**

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
  changed_files_any = ["agents/tasks/LJ-1-413/Probe413.agda"]
  changed_files_none = ["agents/tasks/LJ-1-413/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  error_class = "unsolved_meta"
  changed_files_any = ["agents/tasks/LJ-1-413/review-of-*.md"]

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
- CANDIDATE archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md
- CANDIDATE archive/src/2026-08-09-rud-route/L/CardinalCount.lagda.md
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
- CANDIDATE dev/literature/truncation-and-selection.md
- CANDIDATE dev/literature/digest.md
- CANDIDATE dev/literature/j-hierarchy.md
- CANDIDATE dev/literature/BIBLIOGRAPHY.md

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
