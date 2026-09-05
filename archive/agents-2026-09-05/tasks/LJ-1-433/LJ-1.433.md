# LJ-1.433: below the ambient least cardinal, `Init` is FALSE

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-433/Probe433.agda`, at a GENERIC ordinal:

    init-fails-below :
        (x : V ℓ) (ox : IsOrd x) → ⟨ ω ∈ˢ x ⟩
      → ⟨ fst (κL (x , isL-ord x ox) ox) ∈ˢ x ⟩
      → Init x → Empty.⊥

`κL` is the ambient least cardinal, SEALED at the call site in the shape
`[LJ-1.421]` seals it (`agents/tasks/LJ-1-421/Probe421.agda:125-135`), with the
same four projections `κL`, `κoL`, `κ∈sucL` and `κ-injL`.

**THE ARROW STAYS TRUNCATED THROUGHOUT.** The goal is `Empty.⊥`, which is a
proposition, so `PT.rec` spends `κ-injL` and nothing untruncates.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-433/Probe433.agda::init-fails-below"]

## SCOPE (write)
- agents/tasks/LJ-1-433/Probe433.agda
- agents/tasks/LJ-1-433/lj-1.433-report.md
- agents/tasks/LJ-1-433/review-of-init-fails-below.md

## PREMISES
- `Init`'s fourth conjunct refutes an injection of the index into an infinite member's square. Basis: src/L/Ordinal/SquareLaw.lagda.md:696
- `Init`'s third conjunct closes the index under successors. Basis: src/L/Ordinal/SquareLaw.lagda.md:695
- The ambient least cardinal delivers its arrow TRUNCATED and never as data. Basis: src/L/Cardinal.lagda.md:133
- The selected index is a member of the successor of the site. Basis: src/L/Cardinal.lagda.md:129
- The selected index is an ordinal, by `mem-ord` along that membership. Basis: src/L/Cardinal.lagda.md:125
- `[LJ-1.421]` proves the selected index is not finite, from the truncated arrow alone. Basis: agents/tasks/LJ-1-421/Probe421.agda:164
- The seal that keeps the wall closed is at four projections and it is copied, not re-measured. Basis: agents/tasks/LJ-1-421/Probe421.agda:125
- Trichotomy on two ordinals is delivered. Basis: src/L/Ordinal/Linear.lagda.md:136
- A member of a set is a member of its successor. Basis: src/V/Model.lagda.md:230
- A set is a member of its own successor. Basis: src/V/Model.lagda.md:236
- The successor of an ordinal is an ordinal. Basis: src/L/Ordinal.lagda.md:96
- A member of an ordinal embeds its index into that ordinal. Basis: src/L/BoundedSubset.lagda.md:1371
- `[LJ-1.406]` pays `Init` at the least cardinal itself, and this task says nothing about that site. Basis: agents/tasks/LJ-1-406/Probe406.agda:180
- The architecture is a CANDIDATE and only a measurement settles it. Basis: dev/pod/screen.toml:10

## WHAT IS DELIVERED ALREADY

**`Init` AT THE LEAST CARDINAL IS PAID.** `init-at-kappa`
(`agents/tasks/LJ-1-406/Probe406.agda:180-190`) delivers `Init (fst κL)` from
the truncated arrow and a truncated induction hypothesis. `[LJ-1.421]` spends it
in case 3 of its split, at `Probe421.agda:248-251`, and that case is the ONE case
of the whole campaign that closes.

**THE SPLIT ITSELF IS DELIVERED.** `kappa-decides`
(`agents/tasks/LJ-1-421/Probe421.agda:182-198`) returns `fst κL ≡ x` or
`⟨ fst κL ∈ x ⟩` by trichotomy.

**THE INFINITUDE IS DELIVERED.** `kappa-not-fin`
(`agents/tasks/LJ-1-421/Probe421.agda:164-180`) refutes `⟨ fst κL ∈ˢ ω ⟩` from
the truncated arrow.

## WHAT IS MISSING

**NOBODY HAS ASKED WHETHER THE OTHER CASE CAN EVER CLOSE THE SAME WAY.** Every
task since `[LJ-1.421]` has attacked case 4 by looking for an arrow as data:
`[LJ-1.422]` at the ambient site, `[LJ-1.424]` and `[LJ-1.431]` at a coded site,
`[LJ-1.432]` at a swapped target. **Not one of them asked the cheaper question:
when `fst κL` is a proper member of `x`, is `Init x` still available at all?**

The answer decides more than this campaign. `[LJ-1.432]` splits on a DIFFERENT
selection, and the case its split leaves open is `fst κC ≡ x`, which it must
close through an initiality at `x`. If `Init x` is FALSE whenever `fst κL ∈ x`,
then that case closes only when `fst κL ≡ x` as well, and every future route that
hopes to reach `sq x` through an ambient initiality at a non-cardinal is dead
before it is priced.

## THE REASONING

**D-10, BEFORE ANY AGDA.** Write in the report, at `file:line`, the four
conjuncts of `Init` (`src/L/Ordinal/SquareLaw.lagda.md:692-698`) and state which
one this refutation spends and which one it consumes as a hypothesis. **The
refutation consumes conjunct 3 and refutes conjunct 4.** If you cannot state that
before you write Agda, stop and report.

**THE SHAPE, AND IT IS SHORT.** Let `κ := fst (κL a ox)` with `a := (x , isL-ord x ox)`.

1. `sucV κ` is an ordinal (`src/L/Ordinal.lagda.md:96`).
2. `⟨ sucV κ ∈ˢ x ⟩` comes from conjunct 3 of the hypothesis `Init x` at the
   membership this task takes as an argument.
3. `⟨ ω ∈ˢ sucV κ ⟩` is the W3 term below.
4. `Empty.⊥` is a proposition, so `PT.rec` opens `κ-injL a ox` and gives
   `down : ⟪ x ⟫ ↪ ⟪ κ ⟫` inside the rec and nowhere else.
5. `e := comp-inj down (ord-emb κ (sucV κ) (suc-ord κoL) (self∈sucV κ))`.
6. Conjunct 4 of `Init x` at `β := sucV κ`, with `f m = (fst e m , fst e m)`
   and injectivity from `snd e` and `cong fst`, returns `Empty.⊥`.

Rebuild `comp-inj` and `ord-emb` in the probe rather than importing
`L.BoundedSubset` for two lemmas of three lines
(`src/L/BoundedSubset.lagda.md:1365-1380`).

**W2 (DD4).** Generic in `x`. Name no band, no numeral and no site. `ω` appears
only where `Init`'s own statement and `kappa-not-fin` put it.

**W3, THE WIDEST UNMEASURED TERM.**

    omega-in-suc-kappa :
        (x : V ℓ) (ox : IsOrd x) → ⟨ ω ∈ˢ x ⟩
      → ⟨ ω ∈ˢ sucV (fst (κL (x , isL-ord x ox) ox)) ⟩

**THE PROBE.** Typecheck `omega-in-suc-kappa` ALONE, with the obligation
omitted, before you write the obligation. It is the one step where the argument
can fail: `kappa-not-fin` refutes `⟨ κ ∈ˢ ω ⟩`, and trichotomy then leaves
`⟨ ω ∈ˢ κ ⟩` or `ω ≡ κ`, and BOTH must land in `⟨ ω ∈ˢ sucV κ ⟩`, the first by
`∈sucV-inl` (`src/V/Model.lagda.md:230`) and the second by `self∈sucV`
(`src/V/Model.lagda.md:236`) after a `subst`. Report wall seconds and peak RSS at
the caliber the program set on your pane, one Agda process, three forced
rechecks, and the median. **If this term does not close, the refutation does not
close, and that is the NO-GO.** Quote the elaborator at `file:line`. A heap event
is a WALL event: report it and stop.

**DO NOT WRITE THE DESCENT AND DO NOT TOUCH `[LJ-1.432]`'s SPLIT.** This task
adds one refutation and nothing else. **Do not import a probe of `[LJ-1.429]`,
`[LJ-1.430]`, `[LJ-1.431]` or `[LJ-1.432]`, and do not copy a type out of any of
their briefs.** None of those tasks has a report you can open. A report you
cannot open is a report you may not cite.

**C-42.** This refutation measures ONE site: the ambient least cardinal of
`x`. In a section `## WHAT THIS DOES NOT MEASURE`, say plainly that it says
nothing about a coded selection, and name at `file:line` the coded predicate
(`src/L/Cardinal.lagda.md:239`) that a different selection would use.

ESTIMATE for the Agda: about 60 code lines. BASIS:
`agents/tasks/LJ-1-421/Probe421.agda:125-180` is the seal plus `kappa-not-fin` in
56 lines, and this task keeps both and adds one conjunct-4 application of about
12 lines. **Comparables of SHAPE and never of size, and nothing may be funded
against them.**

## WHAT GO AND NO-GO EACH EARN

**A GO IS A REFUTATION AND IT CLOSES A FAMILY OF ROUTES.** It says: `Init x`
holds only when `x` is its own ambient least cardinal. Every route that hoped to
reach `sq x` at a non-cardinal `x` through an ambient initiality is then priced
out, and `[LJ-1.432]`'s open case is priced with it. Say in the report, as one
sentence with a `file:line`, what this leaves as the only remaining producer of
`sq` at a non-cardinal.

**A NO-GO IS WORTH AS MUCH.** It says the tree cannot get `⟨ ω ∈ˢ sucV κ ⟩`, or
cannot spend conjunct 3, and it names which. That is a measured fact about `Init`
that the campaign has assumed in both directions and never checked.

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
  changed_files_any = ["agents/tasks/LJ-1-433/Probe433.agda"]
  changed_files_none = ["agents/tasks/LJ-1-433/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-433/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 201.177)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 178.553)
- CANDIDATE archive/dev/JOURNAL.md  (score 137.545)
- CANDIDATE dev/ARCHIVE.md  (score 136.522)
- CANDIDATE archive/dev/STATUS-archived.md  (score 108.444)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 81.998)
- CANDIDATE dev/literature/devlin-II5.md  (score 51.110)
- CANDIDATE dev/literature/terms-2026-08.md  (score 50.014)
- CANDIDATE dev/literature/digest.md  (score 39.141)
- CANDIDATE dev/literature/geology.md  (score 29.092)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
