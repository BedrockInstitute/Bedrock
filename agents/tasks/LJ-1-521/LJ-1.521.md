# LJ-1.521: the adequacy, which ten dispatches have been building toward

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-521/Probe521.agda`:

    rankFo-adequate′ :
        (Q a : S) (oa : IsOrd (fst a)) (z : S)
      → ord-reads-Q Q a oa
      → ⟨ (z ∷ []) ⊨ rankFo Q a ⟩
      → Σ[ m ∈ S ] Σ[ mx ∈ ⟨ fst m ∈ fst a ⟩ ]
          (fst z ≡ pr (fst m) (fst (rank-at′ a oa m mx)))

**exactly as `[LJ-1.518]` restated it, with no holes.** Land nothing in `src/`.

**`[LJ-1.518]` IS GO AND IT CLOSED THE LAST NAMED GAP.** `ord-reads-Q` is
stated (`agents/tasks/LJ-1-518/Probe518.agda:184-185`) **and inhabited at the
∈-order** (`:340-342`), which is what the brief demanded and what
`[LJ-1.507]`'s empty antecedent taught this campaign to demand.

**TEN OF ELEVEN INPUTS ARE DELIVERED AND `[LJ-1.518]` LISTED THEM.**

| input | where |
|---|---|
| `rankFo` | `agents/tasks/LJ-1-497/Probe497.agda:255-264` |
| `ord-reads-Q` and its witness | `agents/tasks/LJ-1-518/Probe518.agda:184-185`, `:340-342` |
| `swo-rank′`, `swo-rank′-ord` | `agents/tasks/LJ-1-515/Probe515.agda:112-113`, `:115-117` |
| the SWO at the site | `agents/tasks/LJ-1-515/Probe515.agda:280-286` |
| `swo-rank′-∅`, `swo-rank′-∅-only` | `agents/tasks/LJ-1-515/Probe515.agda:218-221`, `:228-231` |
| the minimal-case bridge | `agents/tasks/LJ-1-518/Probe518.agda:446-459` |
| the domain reading | `agents/tasks/LJ-1-518/Probe518.agda:423-437` |
| the empty rank slot at a Q-minimal member | `agents/tasks/LJ-1-497/Probe497.agda:329-334` |

**THE ELEVENTH IS `rank-at′` AND `[LJ-1.518]` WROTE IT OUT.** It is the same
five lines as `[LJ-1.497]`'s `rank-at` (`Probe497.agda:203-207`) with
`swo-rank′` in place of the refuted `swo-rank`:

    rank-at′ : (a : S) (oa : IsOrd (fst a)) (m : S) → ⟨ fst m ∈ fst a ⟩ → S
    rank-at′ a oa m mx = r , isL-ord r (swo-rank′-ord w k)
      where
      w = OrdSWO∈ₛ.w (fst a) oa
      k = fiber (fst a) mx .fst
      r = swo-rank′ w k

`isL-ord` is at `Probe497.agda:149-150`. **Build `rank-at′` first; it is a step
and not the obligation.** `[LJ-1.518]` records that its `k` is that report's
`ix` (`Probe518.agda:95-96`), so the hypothesis and the adequacy name the same
index with no adapter between them.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-521/Probe521.agda::rankFo-adequate′"]

## SCOPE (write)
- agents/tasks/LJ-1-521/Probe521.agda
- agents/tasks/LJ-1-521/lj-1.521-report.md
- agents/tasks/LJ-1-521/review-of-rankFo-adequate-prime.md
- agents/tasks/LJ-1-521/runs/

## PREMISES

1. `[LJ-1.518]` is GO and restated this statement with no holes. Basis: agents/tasks/LJ-1-518/lj-1.518-report.md:3
2. `ord-reads-Q` is stated. Basis: agents/tasks/LJ-1-518/Probe518.agda:184
3. It is inhabited at the ∈-order. Basis: agents/tasks/LJ-1-518/Probe518.agda:340
4. `rank-at′` is the one input not delivered, written out in that report. Basis: agents/tasks/LJ-1-518/Probe518.agda:95
5. `rank-at`, its refuted predecessor, is in `[LJ-1.497]`'s probe. Basis: agents/tasks/LJ-1-497/Probe497.agda:203
6. `isL-ord` packages a rank as a model element. Basis: agents/tasks/LJ-1-497/Probe497.agda:149
7. `rankFo` is delivered. Basis: agents/tasks/LJ-1-497/Probe497.agda:255
8. `swo-rank′` and its ordinality are delivered. Basis: agents/tasks/LJ-1-515/Probe515.agda:112
9. `swo-rank′-∅` is proved. Basis: agents/tasks/LJ-1-515/Probe515.agda:218
10. The SWO at the site is delivered. Basis: agents/tasks/LJ-1-515/Probe515.agda:280
11. `[LJ-1.497]` refuted the OLD adequacy, which this replaces. Basis: agents/tasks/LJ-1-497/Probe497.agda:435
12. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
13. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
14. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**ELEVEN DISPATCHES BUILT THIS ROUTE, ONE REFUTED IT, AND THREE REPAIRED IT.**
`[LJ-1.497]` refuted the old adequacy, `[LJ-1.513]` removed the universe
obstruction, `[LJ-1.515]` delivered the replacement rank and proved it `∅` at a
minimal element, `[LJ-1.518]` stated and inhabited the missing hypothesis.
**This is the term they were for.**

## THE REASONING

**D-10, BEFORE ANY AGDA.** `[LJ-1.518]` says its `k` and `rank-at′`'s `k` are
the same `fiber` line. **Check that at `file:line` before you build.** If the
two indices differ, an adapter is needed and the statement is not the one
`[LJ-1.518]` restated. Say so and STOP rather than inserting one silently.

**CHECK NON-VACUITY BEFORE YOU CELEBRATE A GREEN TERM.** `[LJ-1.507]` proved
that three dispatches of this session built toward a statement nothing
satisfied. **`[LJ-1.518]` inhabited `ord-reads-Q`, so the antecedent is known
non-empty; say in the report which witness you used and where it came from.**

**DO NOT WEAKEN THE CONCLUSION.** The equality `fst z ≡ pr (fst m) (fst
(rank-at′ a oa m mx))` is what `range-clause` consumes. A statement that
concludes less pays nothing.

**DO NOT REVERT TO `swo-rank`.** `[LJ-1.497]` refuted its adequacy and
`[LJ-1.515]` replaced it. If `swo-rank′` will not serve, that is a finding
about the replacement and not a reason to restore the refuted rank.

**DO NOT ATTEMPT `range-clause` OR ANY `InjCode` CONJUNCT.** AD12 gives this
brief one obligation. `[LJ-1.490]` measured that all four want this adequacy;
they are the next task, not this one.

**DO NOT POSTULATE.**

**REQUIRED REPORT SECTION `## WHAT THE FOUR CONJUNCTS NEED NOW`.** With this
term in hand, say for each of `svAt`, `domAt`, `injAt` and the range clause
whether every input is delivered, at `file:line`. **Do not build them.**
`[LJ-1.490]` reported that all four read the second component of a pair in the
carve and want the same adequacy (`agents/tasks/LJ-1-490/lj-1.490-report.md:275`).

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 220 lines in the probe, of which the obligation is
about 60 and `rank-at′` about 8. BASIS: `[LJ-1.518]` rebuilt this telescope,
the hypothesis and its witness in a comparable file. Comparables are of SHAPE
and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the minimal case, because `[LJ-1.497]`'s refutation lived exactly there
and `swo-rank′-∅` was built to answer it.

    -- the adequacy at a Q-minimal member of `a`, alone

**Write it FIRST, with the general case omitted, and typecheck it ALONE.** That
is the case the old rank got wrong. If the new one gets it right, the general
case is the recursion; if it does not, the replacement rank has not fixed what
it was built to fix.

ESTIMATE for W3: about 30 lines and under 45 seconds. **Do not fund it against
`[LJ-1.518]`'s numbers**: that stated a hypothesis and this discharges one.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO CLOSES THE ADEQUACY THAT ELEVEN DISPATCHES HAVE BEEN BUILDING TOWARD**,
and leaves the counting leg with the four conjuncts and nothing else named.

**A NO-GO SAYS THE REPLACEMENT RANK DOES NOT FIX WHAT IT WAS BUILT TO FIX**,
which would send the counting leg back for a ruling with the whole chain
measured behind it. **That is a real outcome and you must not avoid it.**

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
id = "accept-failed"
priority = 14
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 1
  # DELTA KEY ADDED 2026-08-22. Without it this row matches an acceptance
  # failure that delivered NOTHING, escalates, and matches again: MEASURED on
  # LJ-1.497, four times to attempt_max in six minutes, every one exit 1 with
  # delta 0. The row exists for the LJ-1.469 case, where the obligation WAS
  # delivered (delta -1) and acceptance failed. Keep it to that case.
  obligations_delta_max = -1
  changed_files_none = ["agents/tasks/LJ-1-521/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-521/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-521/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-521/Probe521.agda"]
  changed_files_none = ["agents/tasks/LJ-1-521/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-521/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 199.423)
- CANDIDATE archive/dev/JOURNAL.md  (score 169.265)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 152.319)
- CANDIDATE dev/ARCHIVE.md  (score 124.834)
- CANDIDATE archive/dev/PLAN-archived.md  (score 117.943)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 56.004)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 42.840)
- CANDIDATE dev/literature/terms-2026-08.md  (score 34.962)
- CANDIDATE dev/literature/digest.md  (score 30.118)
- CANDIDATE dev/literature/geology.md  (score 25.496)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
