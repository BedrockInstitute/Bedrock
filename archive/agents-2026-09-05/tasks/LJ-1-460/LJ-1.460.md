# LJ-1.460: the code this tree already carved, and nobody has claimed it

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-460/Probe460.agda`:

    shift-coded :
        (γ : S) (oγ : IsOrd (fst γ)) (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
        (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩)
      → ∥ Σ[ F ∈ S ] InjCode F (sucʟ γ) γ ∥₁

**A CODE FOR A NON-IDENTITY INJECTION. THIS TREE HAS NEVER HAD ONE.** Land
nothing in `src/`.

**THE GRAPH IS ALREADY CARVED AND IT IS IN `src/`.** `ShiftGraph`
(`src/L/Absorption.lagda.md:538`) opens its own `Carve` publicly at `:604-605`,
which separates the shift's graph into `G` by ONE separation over a named bound
(`:410-412`) and exports both readings, `G-out` (`:415`) and `G-in` (`:420`).
The shift is `sucV γ ↪ γ` (`src/L/Absorption.lagda.md:614-617`). **HALF A, the
step that failed three times for a `leastOf`-selected function, is DELIVERED for
this one because this function is definable.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-460/Probe460.agda::shift-coded"]

## SCOPE (write)
- agents/tasks/LJ-1-460/Probe460.agda
- agents/tasks/LJ-1-460/lj-1.460-report.md
- agents/tasks/LJ-1-460/review-of-shift-coded.md
- agents/tasks/LJ-1-460/runs/

## PREMISES

1. `ShiftGraph` carves the shift's graph as an L-element by one separation, and exports it publicly. Basis: src/L/Absorption.lagda.md:604
2. The carve's `G` is sealed and its two readings are exported. Basis: src/L/Absorption.lagda.md:411
3. The shift itself is an ambient injection from the successor into the ordinal. Basis: src/L/Absorption.lagda.md:614
4. `InjCode` is four conjuncts: three satisfaction facts and one range clause. Basis: src/L/Cardinal.lagda.md:223
5. Only the fourth conjunct mentions the third argument, and only through `fst`. Basis: src/L/Cardinal.lagda.md:228
6. `[LJ-1.414]` is GREEN on HALF B, the four conjuncts from the readings, under four hypotheses. Basis: agents/tasks/LJ-1-414/Probe414.agda:115
7. **AND ITS REPORT OVER-CLAIMED, WHICH THE AUDIT MEASURED.** `[LJ-1.414]` never joined HALF A to HALF B. Basis: dev/pod/audit-2026-08-20.md:83
8. `[LJ-1.429]` is GO on a code at a bound, so this route has produced a code before. Basis: agents/tasks/LJ-1-429/lj-1.429-report.md:84
9. `amb-to-coded` is NO-GO three times, and every one asked for the graph of a `leastOf` selection. Basis: agents/tasks/LJ-1-441/lj-1.441-report.md:53
10. A refutation measures the site it names and never how far that site extends. Basis: dev/LESSONS.md:3752
11. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THE CAMPAIGN SPENT SIXTY DISPATCHES ON HALF A AND A LANDED CHAPTER HAS HELD IT
ALL ALONG, FOR ONE FUNCTION.** `L.Absorption` is inside a proved trophy's
reach. Its `Carve` (`:385-425`) is the same one separation `L.InjChain`'s carve
uses, at the shift's own formula, and `ShiftGraph` instantiates it with
`hasSeparationL` (`:604-605`).

`grep -rn "ShiftGraph" src/` outside that chapter is what this task must run
first and report. **The graph has no consumer.**

## WHAT IS MISSING

The four conjuncts. The graph is a set; `InjCode` wants satisfaction facts.

## THE REASONING

**WHY THIS IS NOT THE STATEMENT THAT FAILED THREE TIMES.** Write it in the
report before any Agda, with both types at `file:line`. `amb-to-coded` asks for
the graph of an ARBITRARY injection, produced by `leastOf`, which carries no
defining formula by construction (`src/L/Cardinal.lagda.md:117`). **The shift is
defined by a formula and the tree already separated on it.** A general negative
about the first says nothing about the second, and C-42 rules that both ways.

**D-10, BEFORE ANY AGDA, AND IT IS THE WHOLE RISK.** `[LJ-1.414]`'s HALF B takes
FOUR hypotheses (`Probe414.agda:115-125`) and the audit measured that 414 never
joined them to anything (`dev/pod/audit-2026-08-20.md:83-89`). **List those four
hypotheses and, for each, say which `ShiftGraph` export supplies it, at
`file:line`.** If one has no supplier, name it and STOP: that missing supplier
is the finding and it outranks the obligation.

**THE SHAPE.** Import `L.Absorption` and `L.Cardinal` from `src/`. Take
`ShiftGraph`'s exports at their delivered types. Rebuild HALF B at
`[LJ-1.414]`'s delivered type or take it as a module hypothesis, and say which
you did. Do not import a probe.

**DO NOT POSTULATE AND DO NOT ADD A HYPOTHESIS TO CLOSE A CONJUNCT.** A telescope
that grows to close a case is the shape audit findings F1 and F3 measured.

**REQUIRED REPORT SECTION `## WHAT A CODE HERE BUYS`.** State, as a type, what
`Residue` asks at `y := sucʟ γ`, and say whether this term supplies it. **Do not
claim `Residue` in general.** This is one site, `[LJ-1.446]` gives the ordering
unconditionally, and one site is not the band.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 150 lines in the probe, of which the obligation is
about 40. BASIS: `agents/tasks/LJ-1-429/Probe429.agda` is 98 lines for a code at
a bound and `[LJ-1.414]`'s HALF B is 14 lines under its four hypotheses.
Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the fourth conjunct, the range clause, because it is the only one that
mentions the codomain.

    range-clause :
      (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩ → ⟨ fst y ∈ fst γ ⟩

**Write it FIRST from `G-out` alone, with the obligation omitted, and typecheck
it ALONE.** `G-out` returns the pair's shape under a truncation
(`src/L/Absorption.lagda.md:415-418`) and the clause's conclusion is an hProp,
so `PT.rec` should spend it. **If the truncation cannot be spent there, the
conjunct is unreachable and the task stops at its cheapest point.**

ESTIMATE for W3: about 12 lines and under 15 seconds. BASIS: it is one `PT.rec`
into a membership, and `src/L/Cardinal.lagda.md:228` is the same clause at the
ambient site.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO PUTS THE FIRST CODE FOR A NON-IDENTITY INJECTION IN THIS TREE**, and it
does it from a chapter that was landed before this campaign began. It would
show the three `amb-to-coded` NO-GOs measure `leastOf`, not this tree's reach.

**A NO-GO IS WORTH AS MUCH.** It would say the four conjuncts need more than a
carved graph, and that is the honest price of a code, measured at the one site
where the graph is free.

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
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-460/review-of-*.md"]
  # THE CRITIC'S OWN RETURN MUST NOT RE-MATCH. It writes
  # `review-of-LJ-1-460-<k>.md` beside the coder's leftover `review-of-*.md`.
  # Without this exclusion the escalation re-escalates itself and `attempt_max`
  # parks the task PERMANENTLY. MEASURED 2026-08-21 on LJ-1.448, 449, 450, 451.
  changed_files_none = ["agents/tasks/LJ-1-460/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-460/Probe460.agda"]
  changed_files_none = ["agents/tasks/LJ-1-460/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-460/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 218.591)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 203.028)
- CANDIDATE archive/dev/JOURNAL.md  (score 163.680)
- CANDIDATE dev/ARCHIVE.md  (score 142.303)
- CANDIDATE archive/dev/DD-archived.md  (score 140.452)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 57.645)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 53.054)
- CANDIDATE dev/literature/terms-2026-08.md  (score 49.180)
- CANDIDATE dev/literature/digest.md  (score 42.507)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 34.326)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
