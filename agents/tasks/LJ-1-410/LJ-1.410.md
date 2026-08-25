# LJ-1.410: the descent, with the infinity conjunct OUT of the predicate

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-410/Probe410.agda`.

    sel-descent-nofin :
        (κ : S) (oκ : IsOrd (fst κ)) → ⟨ ω ∈ˢ fst κ ⟩
      → (ne : ∥ Σ[ δ ∈ Mem (Lset (SiteBound.β κ)) ] ⟨ Good° κ oκ δ ⟩ ∥₁)
      → Σ[ δ ∈ S ] ( ⟨ fst δ ∈ fst κ ⟩
                   × (⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥)
                   × (⟪ fst κ ⟫ ↪ ⟪ fst δ ⟫) )

with `Good°` carrying TWO conjuncts and not three:

    Good° κ oκ δ = ( ⟨ fst (up δ) ∈ fst κ ⟩
                   × ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) κ (up δ) ∥₁ )
                 , <isProp>

**THIS IS `[LJ-1.403]` WITH ITS INFINITY CONJUNCT MOVED FROM THE PREDICATE TO
THE CONCLUSION, AND SPELLED THE WAY THE CONSUMER SPELLS IT.**

**IT TAKES `[LJ-1.401]`'s `isPropInjCode` AND `[LJ-1.402]`'s `sel-arrow` AS
MODULE HYPOTHESES**, at the types `[LJ-1.403]` used
(`agents/tasks/LJ-1-403/Probe403.agda:82` and `:83`). Do not import either probe
and do not rebuild them. Do not import `Probe403` either: rebuild the selection,
because its predicate changes.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-410/Probe410.agda::sel-descent-nofin"]

## SCOPE (write)
- agents/tasks/LJ-1-410/Probe410.agda
- agents/tasks/LJ-1-410/lj-1.410-report.md

## PREMISES
- The consumer states infiniteness as `⟨ δ ∈ ω ⟩ → Empty.⊥`, never as `⟨ ω ∈ δ ⟩`. Basis: src/L/StageCardinal.lagda.md:17
- `[LJ-1.403]` put `⟨ ω ∈ fst (up δ) ⟩` INSIDE the selection predicate. Basis: agents/tasks/LJ-1-403/Probe403.agda:45
- `[LJ-1.403]` then owed three gap types to any caller, and its third is that conjunct. Basis: agents/tasks/LJ-1-403/lj-1.403-report.md:164
- `[LJ-1.403]` recorded that gap 3 can fail at a finite member of an infinite ordinal, so it is a truth question and not a proof question. Basis: agents/tasks/LJ-1-403/lj-1.403-report.md:180
- `no-fin-descent` derives「the target is not finite」FROM the arrow, and it is green at 8 code lines. Basis: agents/tasks/LJ-1-398/Probe398.agda:213
- `finite-excl-ω` is the delivered refutation `no-fin-descent` runs on. Basis: src/L/InjChain.lagda.md:153
- `leastOf` returns data from a truncated non-emptiness whenever the predicate is an hProp. Basis: src/L/WellOrder/Base.lagda.md:158
- Membership is an hProp, so it may sit in a `leastOf` predicate for free. Basis: src/L/WellOrder/Base.lagda.md:159
- `[LJ-1.404]` REFUTED the `⟨ ω ∈ ... ⟩` form at the selected cardinal, so the `∈ ω → ⊥` form is the only honest one. Basis: agents/tasks/LJ-1-404/lj-1.404-report.md:18
- `Good` is an hProp only because its code existential is truncated. Basis: src/L/Cardinal.lagda.md:240

## WHAT IS DELIVERED ALREADY

**THE ASSEMBLY.** `[LJ-1.403]` built `sel-descent` at 31 non-blank code lines
and it is green (`agents/tasks/LJ-1-403/lj-1.403-report.md:56`). Its three
steps are the ones this task repeats: one strengthened selection, then
`[LJ-1.401]`, then `[LJ-1.402]`.

**THE RECOVERY.** `no-fin-descent` (`agents/tasks/LJ-1-398/Probe398.agda:213-220`)
turns an arrow out of an infinite ordinal into「the target is not finite」in
eight code lines, and its conclusion is `Empty.⊥`.

## WHAT IS MISSING

**THE TWO HALVES HAVE NEVER MET.** `[LJ-1.403]` put infinity in the predicate
and then owed a caller a conjunct that can be FALSE. `[LJ-1.398]` derived
infinity from the arrow and never touched the predicate. Nobody has run the
selection with the weaker predicate and recovered infinity afterwards.

## THE REASONING

**GAP 3 IS NOT A GAP. IT IS A CONJUNCT THAT SHOULD NEVER HAVE ENTERED THE
PREDICATE.** `[LJ-1.403]` asked a caller for

    inf-δ : (κ)(oκ)(δ) → ⟨ ω ∈ fst κ ⟩ → ⟨ fst δ ∈ fst κ ⟩ → ⟨ ω ∈ fst δ ⟩

and said in the same paragraph that it「can fail at a finite member of an
infinite ordinal」(`agents/tasks/LJ-1-403/lj-1.403-report.md:180-182`). It can.
A caller cannot be asked for it. **But nothing needs it**: the selected `δ`
receives an arrow OUT of `κ`, and `κ` holds `ω`, so `δ` cannot be finite. The
infiniteness is a CONSEQUENCE of the descent, not a condition on it.

**THE FOUR STEPS.**

1. `Good°`, two conjuncts, and its `isProp`. `[LJ-1.403]` measured that
   `isProp×` and `squash₁` must be RIGHT-associated at `hProp (ℓ-suc ℓ)` and
   that a left-associated packing fails (`agents/tasks/LJ-1-403/lj-1.403-report.md:32-40`).
   With one conjunct fewer the packing is one `isProp×`, not two.
2. `leastOf (orderAt β oβ) lem Good° ne`. The membership conjunct comes back as
   a projection, exactly as before.
3. `isPropInjCode` and a second `leastOf` turn the truncated code into data;
   `sel-arrow` reads it back to `⟪ fst κ ⟫ ↪ ⟪ fst δ ⟫`.
4. **THE NEW STEP.** Feed that arrow and `⟨ ω ∈ˢ fst κ ⟩` to `no-fin-descent`'s
   device and get `⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥`. Rebuild the eight lines; do not
   import `Probe398`.

**WHAT THE CALLER THEN OWES, AND SAY IT AS A TYPE.** `[LJ-1.403]`'s
`CallerNe⁺` had three gaps (`agents/tasks/LJ-1-403/Probe403.agda:65-69`). With
this predicate it has two, both placements, and `[LJ-1.409]` is dispatched
against exactly those two. **State the remaining caller obligation as a type in
your report**, the way `[LJ-1.403]` stated its three, because the next brief is
written from it.

**DO NOT PUT THE BAND MEMBERSHIP IN.** The band is the recursion's context and
not this term's; `[LJ-1.395]` and `[LJ-1.398]` both left it out
(`agents/tasks/LJ-1-398/Probe398.agda:206-209`).

**W2 (DD4).** `Good°` and the selection are generic in `κ`. Name no cardinal
and no numeral except `ω`.

**W3, THE WIDEST UNMEASURED TERM.** It is STEP 4, the recovery at the SELECTED
`δ`, because the arrow it consumes is the one `sel-arrow` produces and because
`[LJ-1.404]` refuted the neighbouring statement at this very site. **The probe
is `nofin-at-selected`: state step 4 ALONE, with the arrow as a bare hypothesis,
run it, and report its code lines before you touch the selection.** ESTIMATE for
the obligation: about 30 code lines. BASIS: `[LJ-1.403]`'s `sel-descent`,
measured at 31 non-blank code lines (`agents/tasks/LJ-1-403/lj-1.403-report.md:56`),
which carries one conjunct more in the predicate and one step fewer at the end,
plus `no-fin-descent` at 8 (`agents/tasks/LJ-1-398/Probe398.agda:213-220`).
**Comparables of SHAPE, not of size, and nothing may be funded against them.**

## WHAT GO AND NO-GO EACH EARN

**A GO RETIRES A GAP THAT CANNOT BE CLOSED AS IT WAS WRITTEN**, and it puts the
descent's conclusion in the consumer's own spelling, so the plug is a match and
not a conversion. With `[LJ-1.409]`, the caller obligation `Ne⁺` then has no gap
left that is a truth question.

**A NO-GO EARNS THE CONJUNCT THAT CANNOT LEAVE THE PREDICATE, AT `file:line`.**
If `Good°` fails to be an hProp, or if the selection needs the infinity conjunct
to run at all, name which and why. **A stated NO-GO is a full return.**

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
  changed_files_any = ["agents/tasks/LJ-1-410/Probe410.agda"]
  changed_files_none = ["agents/tasks/LJ-1-410/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "done"
outcome = "no-go"

  [branch.when]
  exit_code = 42
  error_class = "unsolved_meta"
  changed_files_any = ["agents/tasks/LJ-1-410/review-of-*.md"]

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
- CANDIDATE archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md
- CANDIDATE archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md
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
- CANDIDATE dev/literature/terms-2026-08.md

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
