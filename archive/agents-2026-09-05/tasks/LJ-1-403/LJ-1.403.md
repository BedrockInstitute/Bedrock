# LJ-1.403: the descent, as data, in the shape the band recursion owes

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-403/Probe403.agda`.

    sel-descent :
        (κ : S) (oκ : IsOrd (fst κ))
      → (ne⁺ : <the strengthened non-emptiness, section THE REASONING>)
      → Σ[ δ ∈ S ] ( ⟨ fst δ ∈ fst κ ⟩
                   × ⟨ ω ∈ fst δ ⟩
                   × (⟪ fst κ ⟫ ↪ ⟪ fst δ ⟫) )

**EVERY FIELD UNTRUNCATED.** This is the payload the band recursion owes at a
negative site: a SMALLER ordinal, INFINITE, with an injection into it, all as
data.

**IT TAKES `[LJ-1.401]`'s `isPropInjCode` AND `[LJ-1.402]`'s `sel-arrow` AS
MODULE HYPOTHESES**, at the types those reports give. Do not import either probe
and do not rebuild them. **If either returned NO-GO, take it as a bare
hypothesis anyway**: this task measures the assembly, and the assembly is worth
measuring under a hypothesis.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-403/Probe403.agda::sel-descent"]

## SCOPE (write)
- agents/tasks/LJ-1-403/Probe403.agda
- agents/tasks/LJ-1-403/lj-1.403-report.md

## PREMISES
- `InternalLeastCard.Selected` selects over `Mem (Lset β)` under `orderAt`, and `orderAt` is the CODE order, not the ordinal order. Basis: src/L/Cardinal.lagda.md:247
- So the selected `δᴸ` carries NO ordinal minimality and no ordinal membership. Basis: src/L/Cardinal.lagda.md:249-253
- `Good` is an hProp because its code existential is TRUNCATED, and that is the only reason. Basis: src/L/Cardinal.lagda.md:240
- `IsCardinalL κ` says no member of `κ` admits a code, so its failure is where a smaller coded ordinal comes from. Basis: src/L/Cardinal.lagda.md:230-233
- A membership `⟨ x ∈ y ⟩` is an hProp by construction, so it may be added to a `leastOf` predicate for free. Basis: src/L/WellOrder/Base.lagda.md:159
- `leastOf` returns data from a truncated non-emptiness, and its predicate is any hProp-valued family. Basis: src/L/WellOrder/Base.lagda.md:158-160
- `isPropIsLeast` is the delivered shape for building such a family's `isProp`. Basis: src/L/WellOrder/Base.lagda.md:133-134
- `up` lifts a `Mem (Lset β)` to an L-element and the chapter already uses it inside the predicate. Basis: src/L/Cardinal.lagda.md:240
- `_↪_`. Basis: src/L/Cardinal.lagda.md:47-48

## WHAT IS DELIVERED ALREADY

**THE SELECTION.** `InternalLeastCard.Selected` runs `leastOf` over
`Mem (Lset β)` and returns `δᴸ` as data with its truncated code witness
(`src/L/Cardinal.lagda.md:247-257`).

**THE DEVICE.** `leastOf` turns a truncated non-emptiness into data whenever the
predicate is an hProp (`src/L/WellOrder/Base.lagda.md:158-160`).

## WHAT IS MISSING

**TWO SIDE CONDITIONS, AND NEITHER FOLLOWS FROM THE SELECTION AS IT STANDS.**
`[LJ-1.402]` delivers the arrow out of `κ` into `δᴸ`, and says nothing about
`δᴸ` being a MEMBER of `κ` or being INFINITE. Without both, the arrow is not a
descent, and the recursion cannot take a step with it.

## THE REASONING

**DO NOT TRY TO DERIVE THE TWO CONDITIONS AFTER THE SELECTION. PUT THEM INSIDE
THE PREDICATE.**

`orderAt` orders codes, not ordinals (`src/L/Cardinal.lagda.md:247`). So being
`orderAt`-least says nothing about where `δᴸ` sits in the ordinal order, and any
attempt to recover `⟨ fst δᴸ ∈ fst κ ⟩` from leastness is chasing a fact the
order does not carry. **That is the trap in this task and it is the reason the
task exists.**

The cure is that `leastOf`'s predicate is ANY hProp-valued family. Membership is
an hProp. So strengthen the predicate to carry what you need:

    Good⁺ : Mem (Lset β) → hProp (ℓ-suc ℓ)
    Good⁺ δ = ( ⟨ fst (up δ) ∈ fst κ ⟩
              × ⟨ ω ∈ fst (up δ) ⟩
              × ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) κ (up δ) ∥₁ )
            , <isProp: isProp× of two memberships and squash₁>

and take `ne⁺ : ∥ Σ[ δ ∈ Mem (Lset β) ] ⟨ Good⁺ δ ⟩ ∥₁` as the hypothesis. Then
`leastOf (orderAt β oβ) lem Good⁺ ne⁺` returns `δ` as data **with both side
conditions as projections**, and the inner code existential is still truncated,
which is exactly what `[LJ-1.401]`'s `isPropInjCode` and a second `leastOf`
convert to data. `[LJ-1.402]`'s `sel-arrow` then reads that code back.

**SO THE ASSEMBLY IS: ONE STRENGTHENED SELECTION, THEN `[LJ-1.401]`, THEN
`[LJ-1.402]`.** Three steps, each delivered or hypothesised, and the only new
content is `Good⁺`'s `isProp` and the plumbing.

**WHERE `ne⁺` COMES FROM, AND IT IS NOT YOUR OBLIGATION.** In the band
recursion's negative case the caller has `¬ IsCardinalL κ` and `⟨ ω ∈ fst κ ⟩`.
`IsCardinalL`'s failure (`src/L/Cardinal.lagda.md:230-233`) gives a member of
`κ` with a code, and the infinity conjunct is the caller's to supply or to
refute. **Take `ne⁺` as a hypothesis and say in the report exactly what a caller
must prove to discharge it.** That sentence is what the next brief is written
from, so make it a type and not a paragraph.

**WHAT THIS DOES NOT GIVE YOU, AND DO NOT CLAIM IT.** It does not discharge
`L.StageCardinal`'s module parameter, it does not build the recursion, and it
does not prove `ne⁺` at any site. It builds the STEP the recursion takes, in the
shape the recursion takes it.

**W2 (DD4).** `Good⁺` and the selection are generic in `κ`. Write them that way,
name no cardinal and no numeral, and answer W2 in the report.

**W3, THE WIDEST UNMEASURED TERM.** It is `Good⁺`'s `isProp`, because it is the
one place where a truncation, two memberships and a product meet, and because
`squash₁` and `isProp×` have to be assembled in the right order at a level the
site fixes. **The probe is `goodplus-isProp`: state `Good⁺` alone with its
`isProp`, run it, and report the number of code lines before you write anything
else.** ESTIMATE for the obligation: about 30 code lines. BASIS: `Good` and its
selection at `src/L/Cardinal.lagda.md:240-258`, a delivered comparable of SHAPE
at 19 code lines, plus `isPropIsLeast` at `src/L/WellOrder/Base.lagda.md:133-134`
at 2 code lines. **Neither is a comparable of size and nothing may be funded
against them.**

## WHAT GO AND NO-GO EACH EARN

**A GO DELIVERS THE BAND RECURSION'S NEGATIVE STEP AS DATA**, and the campaign's
open item falls from「the arrow is unreachable」to「`ne⁺` at each site」, which is
a hypothesis about ONE ordinal rather than a missing device.

**A NO-GO EARNS THE CONJUNCT THAT CANNOT ENTER THE PREDICATE, AT `file:line`.**
If `⟨ ω ∈ fst (up δ) ⟩` cannot be carried, or if `Good⁺` fails to be an hProp at
this level, say which and why. That re-plans the split itself. **A stated NO-GO
is a full return.**

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
  changed_files_any = ["agents/tasks/LJ-1-403/Probe403.agda"]
  changed_files_none = ["agents/tasks/LJ-1-403/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  error_class = "unsolved_meta"
  changed_files_any = ["agents/tasks/LJ-1-403/review-of-*.md"]

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
- CANDIDATE archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md  (score 49.330)
- CANDIDATE archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md  (score 43.118)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 38.774)
- CANDIDATE archive/dev/TASKS-archived.md  (score 31.660)
- CANDIDATE dev/ARCHIVE.md  (score 27.209)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 64.881)
- CANDIDATE dev/literature/devlin-II5.md  (score 25.440)
- CANDIDATE dev/literature/terms-2026-08.md  (score 20.117)
- CANDIDATE dev/literature/digest.md  (score 18.902)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
