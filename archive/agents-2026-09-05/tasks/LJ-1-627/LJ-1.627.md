# LJ-1.627: code DATA at the ambient-least ordinal, which finishes (iii) for free

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-627/Probe627.agda`:

    codes-at-kappaL : <a code, AS DATA and not under a truncation, at the
                       ambient-least ordinal `κL`>

Land nothing in `src/`. **Data, not `∥ … ∥₁`. That distinction is the task.**

**ITS HOME, IF IT HOLDS.** `[LJ-1.625]` sited ingredient (v) at
`L.Choice.Faithful`, which imports `L.Coding.CodeSet` with `keyS`, `AllCodes`
and `AllCodes-out` in its `using` (`src/L/Choice/Faithful.lagda.md:63-65`).
**Say in your report whether this term belongs there or elsewhere.**

**`[LJ-1.623]` IS A NO-GO, AND IT NAMED THIS AS THE FIRST OF TWO REOPENERS:**

> "**Codes at the ambient-least ordinal, as data.** The probe consumes them
> (`agents/tasks/LJ-1-623/Probe623.agda:140-148`). **Any future supply that
> produces code DATA at `κL` finishes ingredient (iii) for free.**"

**THE PROBE ALREADY CONSUMES THEM, SO THE INTERFACE IS WRITTEN AND NOT YOURS TO
INVENT.** Read `Probe623.agda:140-148` and take the shape from there.

**WHY THIS AND NOT THE OTHER REOPENER.** `[LJ-1.623]`'s second is
`AmbientToCoded` as an owner-ruled AXIOM, and it measured that it is **not a
construction**. That is a ruling and I have carried it to the owner rather than
queue it. **This one is a construction, so it is the one that gets funded.**

**WHAT `[LJ-1.623]` CLOSED, SO YOU DO NOT REOPEN IT BY ACCIDENT.** At the site
grain the tree pays exactly three ways: through the initial ordinals
(`site-at-init`, from `src/L/Ordinal/SquareLaw.lagda.md:960-961`), through the
band product (`band-pays-site`), or through the residue. **An arbitrary site is
neither of the first two and the third is `[LJ-1.618]`'s wall.** `κL` is not an
arbitrary site: it is the ambient-least. **That is the whole difference and it
is why this brief exists.**

**LITERATURE STEP, REQUIRED.** `dev/literature/truncation-and-selection.md`
section 2.4: Kraus, Escardó, Coquand and Altenkirch, LMCS 13(1) 2017,
arXiv:1610.03346. **Theorem 16: a type has a constant endomap IFF it has split
support.** Theorem 17: merely weakly constant suffices. **Producing DATA where
the tree has a truncation is exactly this question. Answer in those terms: does
the code type at `κL` have a weakly constant endomap?** Do not re-derive the
criterion.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-627/Probe627.agda::codes-at-kappaL"]

## SCOPE (write)
- agents/tasks/LJ-1-627/Probe627.agda
- agents/tasks/LJ-1-627/lj-1.627-report.md
- agents/tasks/LJ-1-627/review-of-codes-at-kappaL.md
- agents/tasks/LJ-1-627/runs/

## PREMISES

1. `[LJ-1.623]` is a NO-GO and names this reopener. Basis: agents/tasks/LJ-1-623/review-of-site-fiber.md:99
2. Its probe consumes the codes. Basis: agents/tasks/LJ-1-623/Probe623.agda:140
3. It closed the site grain as a supply route. Basis: agents/tasks/LJ-1-623/review-of-site-fiber.md:85
4. `site-at-init` pays through the initial ordinals. Basis: src/L/Ordinal/SquareLaw.lagda.md:960
5. `[LJ-1.617]` measured the demand at the site grain. Basis: agents/tasks/LJ-1-617/lj-1.617-report.md:1
6. `[LJ-1.618]` is the residue's wall. Basis: agents/tasks/LJ-1-618/lj-1.618-report.md:1
7. `[LJ-1.625]` sited ingredient (v) at `L.Choice.Faithful`. Basis: src/L/Choice/Faithful.lagda.md:63
8. Kraus Theorem 16 is the untruncation criterion. Basis: dev/literature/truncation-and-selection.md:150
9. `InjCode` is a proposition at today's tree. Basis: agents/tasks/LJ-1-576/Probe576.agda:77
10. `[LJ-1.613]` paid ingredients (i) and (ii). Basis: agents/tasks/LJ-1-613/Probe613.agda:137
11. R-42 rules the respelling cost. Basis: dev/LESSONS.md:4404
12. A stop is a deliverable. Basis: AGENTS.md:43
13. `make check` is the gate before any commit. Basis: AGENTS.md:74

## WHAT IS DELIVERED ALREADY

A consumer for these codes, written and typechecked, and three closed supply
routes at an arbitrary site. **No code data at `κL`.**

## THE REASONING

**D-10, BEFORE ANY AGDA, AND IT IS THE CONSUMER.** Read
`agents/tasks/LJ-1-623/Probe623.agda:140-148` and state at `file:line` **exactly
what shape of data it consumes.** Build to that shape and nothing wider.

**`κL` IS THE AMBIENT-LEAST AND THAT IS THE ONLY REASON THIS IS NOT `[LJ-1.618]`
AGAIN.** Say at `file:line` **what leastness gives you that an arbitrary site
does not.** If the answer is nothing, this is `[LJ-1.618]`'s wall under another
name and you should stop and say so.

**DATA, NOT A TRUNCATION.** If you can only produce `∥ … ∥₁`, that is
`[LJ-1.623]`'s residue and not this obligation. **Say so and stop.**

**MEASURE THE FLOOR FIRST, PEAK RSS AND SECONDS, AND SET AND REPORT YOUR OWN
WALL-CLOCK CAP.**

**DO NOT ATTEMPT `AmbientToCoded`.** `[LJ-1.623]` measured it is not a
construction, and it is with the owner as a ruling.

**DO NOT POSTULATE. DO NOT LAND IN `src/`. NEVER COMMIT AND NEVER PUSH.**

**REQUIRED REPORT SECTION `## WHAT LEASTNESS BUYS`.** At `file:line`, or the
sentence that it buys nothing.

**REQUIRED REPORT SECTION `## DOES (iii) CLOSE`.** `[LJ-1.623]` says this
finishes ingredient (iii) for free. **Say whether it does, and do not read a
discharge into anything you did not inhabit.**

**REQUIRED LITERATURE STEP** as above.

ESTIMATE: about 170 lines in the probe, of which the obligation is about 45.
BASIS: `[LJ-1.623]` built the consumer at a comparable size. **Uncertain: this
is the fourth object in this family and three have been walls.** Comparables are
of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the code type at `κL`.

    -- the code type at the ambient-least ordinal, TYPE ONLY, capped

**Write it FIRST, typecheck it ALONE, cap it.** ESTIMATE: about 12 lines, cap at
two minutes.

## WHAT GO AND NO-GO EACH EARN

**A GO FINISHES INGREDIENT (iii)**, and with (i), (ii), (iv) and (v) paid the
`class-pred` formula's supplies would be complete.

**A NO-GO SHOWING LEASTNESS BUYS NOTHING LEAVES ONLY THE AXIOM**, and then the
owner's ruling on `AmbientToCoded` is the campaign's only remaining move on this
row. That is worth knowing in the hour it lands.

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
  changed_files_none = ["agents/tasks/LJ-1-627/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-627/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-627/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-627/Probe627.agda"]
  changed_files_none = ["agents/tasks/LJ-1-627/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-627/review-of-*.md"]

[[branch]]
# PARK, NOT ESCALATE. MEASURED on LJ-1.534, 2026-08-22: this row matched
# a heap wall FOUR times, exit 251 each, to attempt_max. A critic
# re-runs the same probe and re-hits the same wall, so an escalation can only
# loop. **A heap wall is a resource fact and no critic can adjudicate it.**
id = "heap-wall-park"
priority = 30
action = "park"

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
  Full entry: dev/LESSONS.md:2307
- **P-l. A statement may be ABOUT a concrete stage without dragging that stage's PRESENTATION into its type**
  **The law.** Being about a concrete position is not what costs. Naming a transparent construction in a statement's TYPE is. If the tower's stage values are `opaque` upstream, a theorem may quantify over, hypothesize about and conclude at `Sset ω` freely, because the stage is an ATOM to the elaborator and nothing unfolds. If instead the type mentions a transparent presentation, such as `⟪ sucV (...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2367
- **D-26. A well-founded key on a tower needs generation data, or it needs syntax**
  **Rule:** When a route must well-order a cumulative tower's stage, ask first what the stage's members CARRY. A stage built as the values of finitely many total operations carries its own generation data, so a well-founded key exists with NO syntax at all: the operation index, then the arguments, ordered recursively. A stage built as a definable power carries nothing: its members are sets, not c...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:1735
- **C-42. A refutation measures the site it names, and it never measures how far that site extends**
  **Rule:** A refutation is a measurement of ONE site. It says the statement there is false. **It says nothing about how many other sites carry the same false shape.** So when a refutation lands, the next action is not the cure. **It is the sweep: search the tree for the shape, and report the COUNT before you price the cure.** A cure funded against the named site is priced against a number nobody...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:3762

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev, archive/scripts, dev/ARCHIVE.md:
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 196.854)
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 192.979)
- CANDIDATE archive/dev/JOURNAL.md  (score 172.445)
- CANDIDATE dev/ARCHIVE.md  (score 161.819)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 157.176)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 78.432)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 62.896)
- CANDIDATE dev/literature/terms-2026-08.md  (score 57.676)
- CANDIDATE dev/literature/digest.md  (score 54.557)
- CANDIDATE dev/literature/geology.md  (score 34.612)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
