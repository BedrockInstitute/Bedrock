# LJ-1.422: untruncate the least-cardinal arrow, or name the device the tree lacks

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-422/Probe422.agda`, at a GENERIC L-element.

    kappa-arrow-data :
        (a : S) (oa : IsOrd (fst a))
      → ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫

`κL` and `κoL` are module hypotheses at `[LJ-1.406]`'s delivered types
(`agents/tasks/LJ-1-406/Probe406.agda:82` and `:85`). The tree already delivers
this arrow TRUNCATED, twice: as `κ-inj` at `src/L/Cardinal.lagda.md:133` and as
`κ-injL` at `agents/tasks/LJ-1-406/Probe406.agda:88`. **This task asks for the
same arrow as DATA. It asks for nothing else.**

**W8 BINDS THIS TASK. READ THE LITERATURE BEFORE ANY AGDA**, and read it for
one question: what device does the orthodox proof use to name this arrow.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-422/Probe422.agda::kappa-arrow-data"]

## SCOPE (write)
- agents/tasks/LJ-1-422/Probe422.agda
- agents/tasks/LJ-1-422/lj-1.422-report.md
- agents/tasks/LJ-1-422/review-of-kappa-arrow-data.md

## PREMISES
- The tree builds the ambient least cardinal by a `leastOf` selection over an ordinal well-order. Basis: src/L/Cardinal.lagda.md:117
- The arrow into it comes out truncated, and the chapter says so in its own comment. Basis: src/L/Cardinal.lagda.md:133
- `[LJ-1.406]` sealed the same arrow, still truncated. Basis: agents/tasks/LJ-1-406/Probe406.agda:88
- `leastOf` untruncates only over a carrier that carries an `SWO`. Basis: src/L/WellOrder/Base.lagda.md:158
- `[LJ-1.417]` delivered a THIRD untruncation device, green, which turns any small `SWO` carrier into an ordinal with no selection. Basis: agents/tasks/LJ-1-417/Probe417.agda:80
- That device rests on a bounding operator that returns a PAIR and not a truncated existence. Basis: src/L/Ordinal.lagda.md:154
- The tower carries a well-order at every ordinal's stage. Basis: src/L/Choice/Step.lagda.md:730
- A stage well-order can be carried down to the small member type. Basis: src/L/Choice/Step.lagda.md:272
- The architecture is a CANDIDATE and only a measurement settles it. Basis: dev/pod/screen.toml:10

## WHAT IS DELIVERED ALREADY

**THREE UNTRUNCATION DEVICES, AND THE THIRD LANDED THIS WEEK.**

1. `PT.rec`, which demands the motive be an hProp.
2. `leastOf`, which demands an `SWO` over the carrier being selected from
   (`src/L/WellOrder/Base.lagda.md:158`).
3. `swo-into-ord`, `[LJ-1.417]`, green: a small type with an `SWO` injects into
   an ordinal, with no `∥ ∥₁` in the result type
   (`agents/tasks/LJ-1-417/Probe417.agda:80`). It COMPUTES a rank rather than
   selecting a witness, and its bound is a pair (`src/L/Ordinal.lagda.md:154`).

**AND `[LJ-1.418]` INSTANTIATED THE THIRD AT THE TOWER**, at every ordinal, with
no `Init` and no band hypothesis. Its report is
`agents/tasks/LJ-1-418/lj-1.418-report.md`.

## WHAT IS MISSING

**THE ENUMERATION THE CAMPAIGN CLOSED ON IS NOT SOUND, AND THE OWNER'S AUDIT
SAYS SO.** `dev/pod/audit-2026-08-20.md` finding F8 records that
`[LJ-1.391]`'s claim「a grep returns no other shape」does not survive a re-run,
and that an independent review of that report was written and never applied.
**Re-enumerate. Do not cite `[LJ-1.391]`'s count.**

**AND THE THIRD DEVICE WAS NOT IN THE TREE WHEN THAT ENUMERATION WAS MADE.**
Whether it covers THIS carrier is unmeasured.

## THE REASONING

**NAME THE CARRIER FIRST, BECAUSE THAT IS WHAT DECIDES THE DEVICE.** The
truncation sits over the type of injections `⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫`.
Ask of each device, in this order, and record the answer for each:

1. **`PT.rec`.** Is the target an hProp? The target is a Sigma of a function and
   a proof. Say why it is or is not, at `file:line`.
2. **`leastOf`.** Does `src/` carry an `SWO` over that carrier, or over one that
   injects into it? **Re-run the enumeration yourself** and report the COUNT and
   the shapes, not a prior report's summary.
3. **`swo-into-ord`.** It ranks a carrier into the ordinals. Does it apply here,
   and if it does, what does it return? Be exact: it returns an injection into
   SOME ordinal, and the task's target is an injection into a NAMED one.

**W2 (DD4).** Generic in `a`. Name no cardinal and no numeral except `ω`.

**D-10, BEFORE ANY AGDA.** The truncated form is delivered, so the statement's
truth is not in question and its DATA is. **But check one thing before you
build: is the untruncated form an hProp-free statement that a constructive tree
may name at all?** An arrow between two ordinal member types, chosen from many,
is a choice of one of several. Say what makes a canonical choice possible here,
or say that nothing does.

**W3, THE WIDEST UNMEASURED TERM.**

    device-covers-carrier

**THE PROBE.** For the ONE device you judge most likely, write the smallest
Agda fragment that applies it to this carrier and typecheck it ALONE. Report
the exact elaboration error if it fails, at `file:line` in your own probe. **One
device, one fragment, one run. Do not attempt all three in Agda.**

ESTIMATE for the Agda: about 20 code lines if a device applies, and about 8 for
the stated fragment if none does. BASIS: `[LJ-1.417]`'s own application of
`boundingOrd` is 18 non-blank lines at `agents/tasks/LJ-1-417/Probe417.agda:80`.
**Comparables of SHAPE and never of size, and nothing may be funded against
them.**

**W8, AND IT IS THE HEART OF THIS TASK.** Read `dev/literature/` for the
orthodox proof that a constructible level has the size of its index, and answer
in a report section `## WHAT THE ORTHODOX PROOF NAMES THIS ARROW WITH`:

- Which theorem supplies the arrow, at `file:line` in `dev/literature/`.
- What device it uses to make the arrow CANONICAL rather than merely existent.
- **Whether that device is in this tree, live, archived, or absent.** The
  archived condensation chapter is
  `archive/src/2026-08-09-rud-route/L/Condensation.lagda.md`. Read its first
  paragraph and say whether it is the device the theorem names.

**A LITERATURE NO-GO IS A FULL RETURN.** If the orthodox route names a device
this tree does not have and cannot reach, stop and say so. That is the answer
`[LJ-2.5]` needs and it is worth more than a partial term.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS `[LJ-1.421]`'s HYPOTHESIS AND, WITH IT, THE CAMPAIGN.** Say which
device paid, and what the tree gains besides this arrow.

**A NO-GO NAMES THE MISSING DEVICE, AND THAT IS AN ARCHITECTURE FACT AND NOT A
ROUTE FACT.** If the orthodox proof reaches this arrow through a device that
lives only on the retired route, then the two-tower candidate has a measured
reason to exist, and `[LJ-2.5]` has its evidence. Say it in one sentence and
name the archived chapter at `file:line`.

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
  changed_files_any = ["agents/tasks/LJ-1-422/Probe422.agda"]
  changed_files_none = ["agents/tasks/LJ-1-422/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-422/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 204.036)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 174.768)
- CANDIDATE archive/dev/JOURNAL.md  (score 151.886)
- CANDIDATE dev/ARCHIVE.md  (score 142.137)
- CANDIDATE archive/dev/DD-archived.md  (score 134.410)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 103.509)
- CANDIDATE dev/literature/devlin-II5.md  (score 64.046)
- CANDIDATE dev/literature/digest.md  (score 50.597)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 44.690)
- CANDIDATE dev/literature/geology.md  (score 43.163)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
