# LJ-1.495: twenty-six of TFacts's fields may be a delivered shift, iterated six times

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-495/Probe495.agda`:

    tfacts-shared-from-kfacts :
        (the KValue frame, rebuilt)
      → KFacts iA iK i0 ... i11 Kenv
      → (the 26 fields TFacts shares with KFacts, at TFacts's own indices)

**by applying `KFactsCons` six times and reading the fields off the result.** Do
not fill the other fields of `TFacts` and do not build a `TFacts` value. Land
nothing in `src/`.

**THE ARITHMETIC MATCHES AND NOBODY HAS CHECKED IT.** `KFacts` is indexed by
`Fin n` over `γ : S ^ n` (`src/L/Condensation.lagda.md:6079-6080`). `TFacts` is
indexed by `Fin (5 + n)` over `γ' : S ^ (11 + n)`
(`src/L/Condensation/TwelveAgree.lagda.md:129-131`), and every shared field looks
its index up under **exactly six** `suc`s, which takes `Fin (5 + n)` to
`Fin (11 + n)`. `KFactsCons` is the one-step shift and its comment says every
field is DEFINITIONALLY the block's own field
(`src/L/Condensation.lagda.md:6119-6128`).

**THE ONE-STEP APPLICATION IS ALREADY IN THE TREE.** `consed`
(`src/L/Condensation.lagda.md:7429-7434`) applies `KFactsCons` to `facts` inside
`KValue`'s own telescope. **You are iterating a delivered move, not inventing
one.**

**THE 26 SHARED NAMES, MEASURED, NOT ESTIMATED:** `tagEq0` to `tagEq11`,
`numK0` to `numK11`, `innerK`, `pairK`. `TFacts` has 59 fields in all
(`src/L/Condensation/TwelveAgree.lagda.md:129-332`). `KFacts` has 29
(`src/L/Condensation.lagda.md:6079-6115`) and carries three the shift discards:
`innerPairK`, `carrierK`, `arityK`.

**DO NOT TAKE `[LJ-1.113]`'s LIST AS THIS ONE.** Its 28 are `SatGraphAgree`
satisfier facts with names such as `subK₁-and`
(`agents/tasks/LJ-1-113/lj-1.113-report.md:48`), and none of them is a `TFacts`
field. **This task says nothing about that count and you must not report on it.**

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-495/Probe495.agda::tfacts-shared-from-kfacts"]

## SCOPE (write)
- agents/tasks/LJ-1-495/Probe495.agda
- agents/tasks/LJ-1-495/lj-1.495-report.md
- agents/tasks/LJ-1-495/review-of-tfacts-shared-from-kfacts.md
- agents/tasks/LJ-1-495/runs/

## PREMISES

1. `KFacts` is indexed by `Fin n` over an environment of length `n`. Basis: src/L/Condensation.lagda.md:6079
2. `TFacts` is indexed by `Fin (5 + n)` over an environment of length `11 + n`. Basis: src/L/Condensation/TwelveAgree.lagda.md:130
3. Its first field looks its index up under six successors. Basis: src/L/Condensation/TwelveAgree.lagda.md:133
4. `KFactsCons` shifts a whole `KFacts` one element deeper. Basis: src/L/Condensation.lagda.md:6122
5. Its comment states the shift is definitional at every field. Basis: src/L/Condensation.lagda.md:6120
6. `consed` is the delivered one-step application inside `KValue`. Basis: src/L/Condensation.lagda.md:7429
7. `KValue` binds the frame this needs. Basis: src/L/Condensation.lagda.md:7380
8. `[LJ-1.491]` is GO and rebuilt that frame at a restricted telescope. Basis: agents/tasks/LJ-1-491/lj-1.491-report.md:200
9. `[LJ-1.113]`'s 28 name a different list. Basis: agents/tasks/LJ-1-113/lj-1.113-report.md:48
10. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
11. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THIS FRONT HAS HAD ELEVEN DISPATCHES AND EVERY ONE WENT AT `someEnv`**, which
is one field of fifty-nine. `[LJ-1.488]` priced its two repairs, `[LJ-1.491]`
found it a home, and `[LJ-1.493]` is pricing the frame now. **No dispatch has
ever asked what the other fields cost.**

## WHAT IS MISSING

The iteration, and the reading.

## THE REASONING

**D-10, BEFORE ANY AGDA.** Count the successors yourself. Say at `file:line`
how many `suc`s `TFacts`'s shared fields carry, what `Fin` the parameters live
in, and what environment length each record uses. **If the shift is not exactly
six, or if the environment lengths do not line up, STOP AND SAY THE TRUE
NUMBERS.** A brief that miscounts an index is a defect and reporting it is worth
more than a term built around it.

**THE SHAPE.** Rebuild `KValue`'s frame. Take its `facts`. Apply `KFactsCons`
six times, each to the result of the last, the way `consed` applies it once.
Then state the 26 fields at `TFacts`'s own indices and fill each by projection.
Do not import a probe.

**DO NOT BUILD A `TFacts` VALUE.** Thirty-three fields are out of scope and AD12
gives this brief one obligation. **Do not fill `someEnv`**, which `[LJ-1.493]` is
measuring this hour, and do not report on it.

**DO NOT POSTULATE AND DO NOT ADD A HYPOTHESIS TO `KFacts`.** If the six-fold
shift does not land on `TFacts`'s indices, that is the finding, and it says the
two records are not the same block at a shift after all.

**REQUIRED REPORT SECTION `## WHAT TFACTS STILL OWES`.** Give the count of
fields this task pays and the count it does not, both measured from
`src/L/Condensation/TwelveAgree.lagda.md`. Group the unpaid ones by family and
name a source for each family at `file:line` where you can see one. **Do not
price them.** That is the mathematician's, and a price from a comparable is not
a price.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 130 lines in the probe, of which the obligation is
about 55, most of it the projections. BASIS: `consed` is 5 lines for one step
and `[LJ-1.491]` rebuilt this frame in a comparable file. Comparables are of
SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the SECOND application, not the sixth, because the first is `consed` and
the tree has never composed two.

    twice : KFacts iA iK i0 ... i11 Kenv
          → KFacts (suc (suc iA)) ... (c2 ∷ c1 ∷ Kenv)

**Write it FIRST, with the obligation omitted, and typecheck it ALONE.** If two
compose, six compose the same way and the rest is projection. If two do not, the
route is closed at its cheapest point and the reason is a type error you can
quote.

ESTIMATE for W3: about 20 lines and under 30 seconds. **Do not fund it against
`consed`**: one application in a chapter is not two in a probe.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO SAYS TWENTY-SIX OF FIFTY-NINE FIELDS ARE A DELIVERED MOVE ITERATED**, and
it would re-price this whole front, which has been costed for months against one
field.

**A NO-GO SAYS THE TWO RECORDS ARE NOT THE SAME BLOCK AT A SHIFT**, which is
worth as much: it would mean the shared names are a coincidence of spelling, and
every future brief on `TFacts` must treat each field as its own obligation.

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
  changed_files_none = ["agents/tasks/LJ-1-495/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-495/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-495/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-495/Probe495.agda"]
  changed_files_none = ["agents/tasks/LJ-1-495/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-495/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 200.673)
- CANDIDATE archive/dev/JOURNAL.md  (score 157.502)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 144.713)
- CANDIDATE dev/ARCHIVE.md  (score 129.422)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 113.889)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 49.477)
- CANDIDATE dev/literature/devlin-II5.md  (score 48.242)
- CANDIDATE dev/literature/digest.md  (score 34.102)
- CANDIDATE dev/literature/geology.md  (score 32.220)
- CANDIDATE dev/literature/terms-2026-08.md  (score 29.578)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
