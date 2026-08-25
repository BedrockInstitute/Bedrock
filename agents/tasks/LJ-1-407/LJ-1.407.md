# LJ-1.407: the TRUNCATED square law at every band ordinal, with NO residue

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-407/Probe407.agda`, in a module that takes
`α₀` and `oα₀` as parameters exactly as `L.StageCardinal` does.

    sq-trunc :
        (δ : V ℓ) → ⟨ δ ∈ˢ sucV α₀ ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
      → ∥ sq δ ∥₁

**THIS IS `L.StageCardinal`'s MODULE PARAMETER WITH `∥ ∥₁` AROUND ITS SIGMA AND
NOTHING ELSE CHANGED** (`src/L/StageCardinal.lagda.md:17-19`). Spell it so, and
state a `ConsumerShape` beside it that repeats the chapter's own type with the
truncation added, as `[LJ-1.398]` did for the untruncated form
(`agents/tasks/LJ-1-398/Probe398.agda:292-296`).

**EVERY CASE MUST CLOSE. THERE IS NO RESIDUE IN THIS TASK AND YOU MAY NOT LEAVE
ONE.** If a case will not close, that is the finding and it is a NO-GO.

**IT TAKES `[LJ-1.406]`'s `init-at-kappa` AS A MODULE HYPOTHESIS**, at the type
that brief names. Do not import `Probe406` and do not rebuild it. **If
`[LJ-1.406]` returned NO-GO, take it as a bare hypothesis anyway**: this task
measures the assembly.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-407/Probe407.agda::sq-trunc"]

## SCOPE (write)
- agents/tasks/LJ-1-407/Probe407.agda
- agents/tasks/LJ-1-407/lj-1.407-report.md

## PREMISES
- The consumer takes the square law as a module parameter over every band ordinal that is not finite. Basis: src/L/StageCardinal.lagda.md:17
- `∈-induction` is the recursion the band uses, and `[LJ-1.398]` already ran it at this shape with a motive that carries no band membership. Basis: agents/tasks/LJ-1-398/Probe398.agda:206
- `squareω` closes the base at `ω`, delivered and green. Basis: src/L/InjChain.lagda.md:184
- `κ-inj` is the arrow into the ambient least cardinal, TRUNCATED. Basis: src/L/Cardinal.lagda.md:132
- `kappa-decides` splits a site against its own ambient least cardinal, and it is green. Basis: agents/tasks/LJ-1-398/Probe398.agda:141
- `no-fin-descent` shows a descent target is not finite, and it is green at 8 code lines. Basis: agents/tasks/LJ-1-398/Probe398.agda:213
- `descent-core` turns an arrow down, an inclusion up and a square law at the target into the square law at the source. Basis: agents/tasks/LJ-1-390/Probe390.agda:110
- `via-col-square` turns `Init α` into `sq α`. Basis: src/L/Ordinal/SquareLaw.lagda.md:960
- `finite-excl-ω` refutes an injection of `ω` into a finite square. Basis: src/L/InjChain.lagda.md:153
- `ord-tri` is the trichotomy the band splits by. Basis: src/L/Ordinal/Linear.lagda.md:136
- The chapter already states a truncated square law at one site, so the shape is its own. Basis: src/L/Ordinal/SquareLaw.lagda.md:955

## WHAT IS DELIVERED ALREADY

**EVERY DEVICE THIS RECURSION NEEDS.** `squareω` (`src/L/InjChain.lagda.md:184`),
`via-col-square` (`src/L/Ordinal/SquareLaw.lagda.md:960`), `κ-inj` and
`κ-min-at` (`src/L/Cardinal.lagda.md:132` and `:140`), `kappa-decides` and
`no-fin-descent` (`agents/tasks/LJ-1-398/Probe398.agda:141` and `:213`),
`descent-core` (`agents/tasks/LJ-1-390/Probe390.agda:110`).

**THE ASSEMBLY AT THE UNTRUNCATED FORM.** `[LJ-1.398]` ran the same `∈-induction`
and reported GO with ONE residue (`agents/tasks/LJ-1-398/lj-1.398-report.md:16-24`).

## WHAT IS MISSING

**NOBODY HAS ASKED WHAT THE RECURSION COSTS WHEN THE CONCLUSION IS TRUNCATED.**
Every assembly since `[LJ-1.384]` carried the conclusion as data, so every
assembly ended owing an untruncated arrow. The truncated conclusion owes none.

## THE REASONING

**THE ONE IDEA: `∥ sq δ ∥₁` IS A PROPOSITION, SO EVERY TRUNCATED INPUT IS FREE.**
`κ-inj` is truncated and the campaign has treated that as the wall. It is a wall
only for a conclusion that is data. Here it is not.

**THE MOTIVE CARRIES NO BAND MEMBERSHIP, AND `[LJ-1.398]` ALREADY MEASURED
THAT.** Its `Goal` is `IsOrd x → (⟨ x ∈ ω ⟩ → Empty.⊥) → sq x`, with the comment
「no band membership (no supplier reads one at a member)」
(`agents/tasks/LJ-1-398/Probe398.agda:206-209`). Take the same motive with the
truncation added. The band argument is then ignored at the plug, exactly as
`plugs-in` ignores it (`agents/tasks/LJ-1-398/Probe398.agda:298-299`), and no
case has to carry a membership step.

**THE FOUR CASES, AND EACH ONE CLOSES.** Run `∈-induction` with the motive

    Goal x = IsOrd x → (⟨ x ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq x ∥₁

At a site `x` with `IH : (δ) → ⟨ δ ∈ˢ x ⟩ → Goal δ`:

1. **`ord-tri x ω`, branch `x ∈ˢ ω`.** Refuted by the infiniteness hypothesis.
2. **Branch `x ≡ ω`.** `squareω`, transported, then `∣ ∣₁`.
3. **Branch `ω ∈ˢ x`, and `kappa-decides` returns `fst κ ≡ x`.** Then
   `init-at-kappa` gives `Init (fst κ)`, transported along `fst κ ≡ x` to
   `Init x`, and `via-col-square` gives `sq x` as DATA. Wrap it. The
   `⟨ ω ∈ˢ fst κ ⟩` that `init-at-kappa` needs comes from `ω ∈ˢ x` and the same
   equality. The `ih` that `init-at-kappa` needs is the recursion's own `IH`,
   composed with the band-membership step of case 4.
4. **Branch `ω ∈ˢ x`, and `kappa-decides` returns `fst κ ∈ˢ x`.** Then:
   `fst κ` is not finite, by `no-fin-descent`
   (`agents/tasks/LJ-1-398/Probe398.agda:213-220`), whose conclusion is
   `Empty.⊥` and which therefore accepts `κ-inj` under `PT.rec` even though
   `no-fin-descent` takes its arrow as data; `IH (fst κ)` then gives
   `∥ sq (fst κ) ∥₁`; the inclusion `⟪ fst κ ⟫ ↪ ⟪ x ⟫` is `mem-incl`, the same
   12 lines (`agents/tasks/LJ-1-398/Probe398.agda:85-99`); and `PT.map2`
   over `κ-inj` and `IH (fst κ)`, with `descent-core` inside, gives
   `∥ sq x ∥₁`.

**THERE IS NO FIFTH CASE.** `[LJ-1.398]` split further, on `IsCardinalL`, and
that split is what produced its residue (`agents/tasks/LJ-1-398/lj-1.398-report.md:55-70`).
**DO NOT SPLIT ON `IsCardinalL` HERE.** No code, no `InjCode`, no
`InternalLeastCard` and no `Ne⁺` appears anywhere in this task. If you find
yourself reaching for one, the case is case 4 and `κ-inj` already pays it.

**W2 (DD4).** The whole recursion is generic in `x`. `α₀` and `oα₀` are the
consumer's own parameters. Name no ordinal and no numeral except `ω`, which is
the base.

**W3, THE WIDEST UNMEASURED TERM.** It is the INFINITENESS OF THE DESCENT
TARGET in case 4, because `[LJ-1.404]` REFUTED the neighbouring statement: at
the selected `κ` you may NOT conclude `⟨ ω ∈ˢ fst κ ⟩`, only that `fst κ` is not
finite (`agents/tasks/LJ-1-404/lj-1.404-report.md:18-24`). So state

    kappa-not-fin : (x : V ℓ) (ox : IsOrd x) → ⟨ ω ∈ˢ x ⟩
                  → (⟨ fst (κL (x , isL-ord x ox) ox) ∈ˢ ω ⟩ → Empty.⊥)

ALONE, run it before you write the recursion, and report its code lines and its
seconds. ESTIMATE for the obligation: about 70 code lines. BASIS:
`[LJ-1.398]`'s assembly, measured at 74 code lines for its motive, its step and
its two obligations (`agents/tasks/LJ-1-398/lj-1.398-report.md:161-169`), which
carries one case more and one truncation fewer. **It is a comparable of SHAPE
and not of size and nothing may be funded against it.**

**THE SEAL.** `[LJ-1.398]` measured an 8 GB heap wall at a transparent
`LeastCardInjL.κ` and cured it with an opaque `κL`
(`agents/tasks/LJ-1-398/lj-1.398-report.md:140-153`). Seal it here too, and
report whether this site needed it.

## WHAT GO AND NO-GO EACH EARN

**A GO IS THE FIRST COMPLETE PROOF OF ANYTHING AT EVERY BAND ORDINAL**, and it
converts the campaign's whole open item into ONE word. Everything the campaign
has owed since `[LJ-1.384]` (`Ne⁺`, `AmbCard`, `InjCode`, the placement, the
coded square law) is then owed for exactly one reason: the consumer wants the
pairing as DATA and this proves it only up to a truncation. `[LJ-1.408]` tests
that consumer.

**A NO-GO EARNS THE CASE THAT RESISTS EVEN TRUNCATED, AT `file:line`**, and that
is a much heavier finding than a GO: it would say the ambient square law fails
at a named class of ordinals for a reason that is not about truncation at all,
and it re-plans the milestone. **A stated NO-GO is a full return.**

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
  changed_files_any = ["agents/tasks/LJ-1-407/Probe407.agda"]
  changed_files_none = ["agents/tasks/LJ-1-407/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  error_class = "unsolved_meta"
  changed_files_any = ["agents/tasks/LJ-1-407/review-of-*.md"]

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
- CANDIDATE archive/dev/JOURNAL-archived.md
- CANDIDATE archive/dev/TASKS-archived.md
- CANDIDATE dev/ARCHIVE.md

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md
- CANDIDATE dev/literature/devlin-II5.md
- CANDIDATE dev/literature/digest.md
- CANDIDATE dev/literature/j-hierarchy.md

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
