# LJ-1.438: pay the bare hypothesis that four delivered probes carry

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-438/Probe438.agda`, at a GENERIC L-element
`a : S` with `oa : IsOrd (fst a)`:

    coded-nonempty :
      ∥ Σ[ d ∈ ⟪ sucV (fst a) ⟫ ]
          ∥ Σ[ F ∈ Mem (Lset γ) ] InjCode (upγ F) a (upα d) ∥₁ ∥₁

`γ` and `upγ` are the bound built FROM the graph and the crossing at that
bound, REBUILT in this file exactly as `[LJ-1.429]` builds them
(`agents/tasks/LJ-1-429/Probe429.agda:67-82`). `upα` is the ambient crossing,
REBUILT exactly as `[LJ-1.430]` builds it
(`agents/tasks/LJ-1-430/Probe430.agda:60-66`).

**THIS TYPE IS THE BARE MODULE HYPOTHESIS OF TWO GREEN PROBES.**
`[LJ-1.430]` takes it bare (`agents/tasks/LJ-1-430/Probe430.agda:86`) and
`[LJ-1.431]` takes it bare as well. Neither inhabits it. `[LJ-1.432]` stands on
`[LJ-1.431]`'s conclusion. So three GO returns and one more rest on a statement
nobody has paid.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-438/Probe438.agda::coded-nonempty"]

## SCOPE (write)
- agents/tasks/LJ-1-438/Probe438.agda
- agents/tasks/LJ-1-438/lj-1.438-report.md
- agents/tasks/LJ-1-438/review-of-coded-nonempty.md

## PREMISES
- `[LJ-1.429]` is GO and it delivers a code at the wide bound. Basis: agents/tasks/LJ-1-429/lj-1.429-report.md:85
- The delivered term is `id-code-wide`, and its target is the SITE ITSELF. Basis: agents/tasks/LJ-1-429/Probe429.agda:97
- The wide bound is built from the graph by `bound2`, and the membership it needs is paid. Basis: agents/tasks/LJ-1-429/Probe429.agda:67
- `[LJ-1.430]` is GO and it carries the target type of this task as a BARE hypothesis. Basis: agents/tasks/LJ-1-430/lj-1.430-report.md:81
- That hypothesis is written at the coded predicate over the ambient carrier. Basis: agents/tasks/LJ-1-430/Probe430.agda:86
- The coded predicate reads the candidate only through the ambient crossing. Basis: agents/tasks/LJ-1-430/Probe430.agda:83
- `InjCode` mentions its THIRD argument at ONE line, and only through `fst`. Basis: src/L/Cardinal.lagda.md:228
- Its first three conjuncts do not mention the third argument at all. Basis: src/L/Cardinal.lagda.md:225
- The chapter's own AMBIENT selection pays the same shape of hypothesis at the site itself. Basis: src/L/Cardinal.lagda.md:112
- The device it uses is the fiber of the site in its own successor, with its equation. Basis: src/L/Cardinal.lagda.md:106
- The architecture is a CANDIDATE and only a measurement settles it. Basis: dev/pod/screen.toml:10

## WHAT IS DELIVERED ALREADY

**THE CODE AT THE SITE ITSELF IS BUILT.** `id-code-wide`
(`agents/tasks/LJ-1-429/Probe429.agda:97-98`) inhabits
`∥ Σ[ F ∈ Mem (Lset γ) ] InjCode (upγ F) a a ∥₁`. The third argument of
`InjCode` there is `a`, the site, and not a member of the ambient carrier.

**THE AMBIENT SELECTION PAYS THE SAME SHAPE.** `nonempty`
(`src/L/Cardinal.lagda.md:112-114`) inhabits
`∥ Σ[ b ∈ ⟪ sucV (fst α) ⟫ ] ⟨ InjP' b ⟩ ∥₁` by taking `b := self`
(`:103-104`) and moving the identity injection along `self-eq` (`:106-107`)
with a `subst`. **That is the exact device this task needs, one predicate
along.**

**`InjCode` READS ITS TARGET THROUGH `fst` AND NOWHERE ELSE.** Conjuncts one to
three name `F` and `a` only (`src/L/Cardinal.lagda.md:225-227`). Conjunct four
ends in `⟨ fst y ∈ fst b ⟩` (`:228`).

## WHAT IS MISSING

**THE ONE STEP FROM `a` TO A MEMBER OF THE AMBIENT CARRIER.** `id-code-wide`
gives the code at `a`. The predicate wants it at `upα d` for some
`d : ⟪ sucV (fst a) ⟫`. The site is a member of its own successor, so `self`
is that `d`, and `self-eq` is the equation between `fst (upα self)` and
`fst a`. Nobody has run that `subst` at the CODED predicate.

Until it runs, `[LJ-1.430]`, `[LJ-1.431]` and `[LJ-1.432]` are conditional
returns, and the queue has been reading them as delivered facts.

## THE REASONING

**D-10, BEFORE ANY AGDA.** Write in the report, at `file:line`, which conjuncts
of `InjCode` (`src/L/Cardinal.lagda.md:223-228`) mention the THIRD argument,
and through what. **If any conjunct reads more of the third argument than its
`fst`, say so and STOP**, because then no `subst` on `fst` can carry the code
across and the route is refuted rather than delayed.

**THE SHAPE, AND IT IS SHORT.**

1. Rebuild `γ`, `oγ` and `upγ` from `[LJ-1.429]` (`Probe429.agda:67-82`), and
   rebuild the graph and `Fg` with it (`:53-95`).
2. Rebuild `hSucα` and `upα` from `[LJ-1.430]` (`Probe430.agda:60-66`).
3. `self := fiber (sucV (fst a)) (self∈sucV (fst a)) .fst` and
   `self-eq := fiber (sucV (fst a)) (self∈sucV (fst a)) .snd`, the two lines
   the chapter writes at `src/L/Cardinal.lagda.md:103-107`.
4. The W3 term below, which moves the code from `a` to `upα self`.
5. `coded-nonempty = ∣ self , <the W3 term> ∣₁`.

**REBUILD, DO NOT IMPORT.** Do not import `LJ-1-429.Probe429`,
`LJ-1-430.Probe430` or `LJ-1-431.Probe431`. Copy the lines you need and name
them in the report.

**W2 (DD4).** Generic in `a` and in `oa`. Name no band, no numeral and no
cardinal. The module takes `lem` and `ℓ` and nothing else.

**W3, THE WIDEST UNMEASURED TERM.**

    code-target-swap :
        (F b b' : S) → fst b ≡ fst b'
      → InjCode F a b → InjCode F a b'

**THE PROBE.** State and typecheck `code-target-swap` ALONE, with the graph,
`γ` and the obligation OMITTED, before you write anything else. It is the one
step where the argument can fail, and it fails in a way that refutes the route
rather than delaying it: if `InjCode` does not depend on its third argument
through `fst` alone, the code built at the site can never be read as a code at
a member of the carrier, and `[LJ-1.430]`'s hypothesis is unpayable by this
device. Report wall seconds and peak RSS at the caliber the program set on
your pane, one Agda process, three forced rechecks, and the median. Quote the
elaborator at `file:line` if it refuses. A heap event is a WALL event: report
it and stop.

**THE `Small` WARNING IS LIVE AT THE GRAPH.** `[LJ-1.425]` records the private
`Small` instance at `src/L/InjChain.lagda.md:552-553` as the 8 g warning. This
task builds a graph, so run the graph part on its own first and report its peak
RSS before you add the swap.

**C-42.** In a section `## WHAT THIS DOES NOT MEASURE`, say plainly that a GO
pays the hypothesis AT THE WIDE BOUND `γ` and at no other bound. Name at
`file:line` the site bound (`src/L/Cardinal.lagda.md:163-172`) that
`[LJ-1.425]` measured, and record that its return was NO-GO on the same shape
(`agents/tasks/LJ-1-425/lj-1.425-report.md:57`). A GO here does not overturn
that; it measures a different bound.

ESTIMATE for the Agda: about 65 code lines. BASIS: two delivered comparables of
SHAPE, `agents/tasks/LJ-1-429/Probe429.agda` at 49 non-blank non-comment lines
for the graph and the wide bound, and `src/L/Cardinal.lagda.md:103-114` at
about 8 lines for the `self` device. **Comparables of SHAPE and never of size,
and nothing may be funded against them.**

## WHAT GO AND NO-GO EACH EARN

**A GO RETIRES A HYPOTHESIS THAT FOUR RETURNS CARRY.** It says the coded
selection at the wide bound is not vacuous, and `[LJ-1.430]`, `[LJ-1.431]` and
`[LJ-1.432]` become unconditional at that bound. Say in the report, in one
sentence with a `file:line`, the exact type you inhabited, so the next brief
can quote it without opening the probe.

**A NO-GO IS WORTH MORE THAN THE GO.** It says the coded route cannot even be
started at the one bound where a code is known to exist, and four green returns
rest on a statement the tree refuses. Name the conjunct, the type and the
elaborator's line.

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
  changed_files_any = ["agents/tasks/LJ-1-438/Probe438.agda"]
  changed_files_none = ["agents/tasks/LJ-1-438/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-438/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 177.952)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 155.092)
- CANDIDATE dev/ARCHIVE.md  (score 150.791)
- CANDIDATE archive/dev/JOURNAL.md  (score 134.313)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 118.426)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 50.276)
- CANDIDATE dev/literature/devlin-II5.md  (score 48.824)
- CANDIDATE dev/literature/digest.md  (score 33.134)
- CANDIDATE dev/literature/geology.md  (score 27.552)
- CANDIDATE dev/literature/devlin-errata.md  (score 27.472)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
