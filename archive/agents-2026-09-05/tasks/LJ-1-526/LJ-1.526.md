# LJ-1.526: does the successor L-cardinal exist, which the whole trophy needs

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-526/Probe526.agda`:

    SuccCardExists :
        (κ : S) → IsOrd (fst κ) → IsCardinalL κ
      → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
      → ∥ Σ[ δ ∈ S ] SuccCardL δ κ ∥₁

**or refute it, or name exactly what it needs.** Land nothing in `src/`.

**`[LJ-1.523]` IS GO AND THIS IS B4, THE FIRST OF SEVEN INPUTS STATED NOWHERE.**
That task priced the bridge from the bounded subset theorem to `GCHStatement` at
the owner's instruction. Its finding: **the bridge type forms with no hole and
no free name, every one of seventeen names resolves in `src/`, and seven inputs
an inhabitant would consume are stated nowhere in the tree**
(`agents/tasks/LJ-1-523/lj-1.523-report.md`, `## THE INPUT LIST`, list B).

**B4 IS FIRST BECAUSE GCH CANNOT PRODUCE ITS `δ` WITHOUT IT.** `GCHStatement`
(`src/L/GCH.lagda.md:59-70`) asserts a `δ` with `SuccCardL δ κ` and two
injections. **No `δ` means no statement to prove, whatever the injections do.**

**THE ARCHIVE HAS MEASURED NEIGHBOURING GROUND AND YOU MUST READ IT.**
`archive/dev/LJ-dispatch-index.md:166` records `[LJ-1.90-A]`: "Orchestrator
audit: IsCardinal is never inhabited. CONFIRMED. Two hits in src: the
definition and the hypothesis. The probe's own kappa, sucV omega, is not a
cardinal either". `:167` records `[LJ-1.91]`: "IsCardinal is ambient, so the
internal omega-1-L does not provably satisfy it. Order types are the widest
term", priced at 490 to 890 lines.

**BUT THOSE FINDINGS ARE ABOUT THE AMBIENT `IsCardinal`, AND THIS OBLIGATION
USES THE INTERNAL `IsCardinalL`.** `IsCardinal` is
`src/L/BoundedSubset.lagda.md:1046-1047`; `IsCardinalL` is
`src/L/Cardinal.lagda.md:230-233`. **They are different predicates and the
distinction is the whole risk.** Say at `file:line` whether `[LJ-1.91]`'s
obstruction transfers to the internal one. **A measured cure does not transfer
by analogy, and neither does a measured obstruction.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-526/Probe526.agda::SuccCardExists"]

## SCOPE (write)
- agents/tasks/LJ-1-526/Probe526.agda
- agents/tasks/LJ-1-526/lj-1.526-report.md
- agents/tasks/LJ-1-526/review-of-SuccCardExists.md
- agents/tasks/LJ-1-526/runs/

## PREMISES

1. `[LJ-1.523]` is GO and priced the bridge. Basis: agents/tasks/LJ-1-523/lj-1.523-report.md:1
2. B4 is stated nowhere in the tree. Basis: agents/tasks/LJ-1-523/Probe523.agda:191
3. `GCHStatement` asserts the `δ`. Basis: src/L/GCH.lagda.md:59
4. `SuccCardL` is what `δ` must satisfy. Basis: src/L/GCH.lagda.md:46
5. `IsCardinalL` is the internal predicate. Basis: src/L/Cardinal.lagda.md:230
6. `IsCardinal` is the ambient one and it is a hypothesis at its consumer. Basis: src/L/BoundedSubset.lagda.md:1046
7. That consumer takes it as a hypothesis and never proves it. Basis: src/L/BoundedSubset.lagda.md:1386
8. `[LJ-1.523]` confirmed the counting leg's `InjCode` is GCH's. Basis: agents/tasks/LJ-1-523/lj-1.523-report.md:1
9. `stage-card-upper` is a delivered ambient shadow of a sibling input. Basis: src/L/StageCardinal.lagda.md:564
10. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THE BRIDGE HAS A BILL FOR THE FIRST TIME.** `[LJ-1.523]` resolved every name
the bridge type mentions and separated the seven unpaid inputs from the three
delivered ones. **B4 is the one that decides whether the statement has a
witness at all.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE PREDICATE.** Read `IsCardinalL`
(`src/L/Cardinal.lagda.md:230-233`) and `IsCardinal`
(`src/L/BoundedSubset.lagda.md:1046-1047`) side by side. **Say at `file:line`
how they differ and whether `[LJ-1.91]`'s ambient obstruction reaches the
internal one.** If it does, say so and STOP: that would mean GCH's `δ` is
unreachable by the route the tree has, which is the largest finding this
campaign could produce and the owner asked for exactly this kind of answer.

**IF IT DOES NOT REACH, BUILD OR PRICE.** Either inhabit `SuccCardExists`, or
name every input it needs at `file:line` with the same three-way split
`[LJ-1.523]` used: delivered in `src/`, delivered in a probe, stated nowhere.

**DO NOT WEAKEN `SuccCardL`.** Its leastness clause
(`src/L/GCH.lagda.md:50-53`) is what makes `δ` THE successor. A `δ` that is
merely some cardinal above `κ` does not prove GCH.

**DO NOT ASSUME A HARTOGS CONSTRUCTION EXISTS.** `[LJ-1.91]` priced an ambient
one at 490 to 890 lines and it was not built. If you need one, that is a
finding, not a step.

**DO NOT POSTULATE.**

**REQUIRED REPORT SECTION `## AMBIENT AGAINST INTERNAL`.** One table: what
`IsCardinal` demands, what `IsCardinalL` demands, and which of the two the tree
can currently inhabit at any set. **`[LJ-1.90-A]` says the ambient answer is
none; say whether the internal answer is the same.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 150 lines in the probe, of which the obligation is
about 40. BASIS: `[LJ-1.523]` opened both chapters and stated ten types in a
comparable file. Comparables are of SHAPE and nothing may be funded against
them.

## W3, THE WIDEST UNMEASURED TERM

It is whether any set at all satisfies `IsCardinalL`, because if none does the
obligation is vacuous in the worst way and every later input is moot.

    someCardinalL : ∥ Σ[ κ ∈ S ] (IsOrd (fst κ) × IsCardinalL κ) ∥₁

**Write it FIRST, and typecheck it ALONE.** `[LJ-1.90-A]` measured that the
ambient predicate has no inhabitant in the tree. **If the internal one has none
either, say so before building anything on it.** This campaign lost three
dispatches to a statement nothing satisfied (`[LJ-1.507]`).

ESTIMATE for W3: about 25 lines and under 40 seconds. **Do not fund it against
`[LJ-1.523]`'s numbers**: that stated types and this looks for a witness.

## WHAT GO AND NO-GO EACH EARN

**A GO GIVES GCH ITS `δ`** and turns six unpaid inputs into five.

**A NO-GO SAYS THE TROPHY'S OWN WITNESS IS UNREACHABLE BY THE PRESENT ROUTE**,
which is the answer the owner asked for and is worth more than any term this
task could build.

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
  changed_files_none = ["agents/tasks/LJ-1-526/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-526/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-526/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-526/Probe526.agda"]
  changed_files_none = ["agents/tasks/LJ-1-526/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-526/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 262.527)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 232.316)
- CANDIDATE archive/dev/JOURNAL.md  (score 209.662)
- CANDIDATE dev/ARCHIVE.md  (score 172.026)
- CANDIDATE archive/dev/DD-archived.md  (score 165.244)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 70.793)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 68.775)
- CANDIDATE dev/literature/digest.md  (score 58.028)
- CANDIDATE dev/literature/geology.md  (score 57.887)
- CANDIDATE dev/literature/terms-2026-08.md  (score 46.465)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
