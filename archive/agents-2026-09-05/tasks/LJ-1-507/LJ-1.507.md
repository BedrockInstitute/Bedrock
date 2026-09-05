# LJ-1.507: someEnv, at last, under the frame hypothesis the tree already owns

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-507/Probe507.agda`:

    someEnv-at-frame :
        (g1 g2 g3 g4 g5 : S) → someEnvDef {9} KV.iK (gam' g1 g2 g3 g4 g5)

**by discharging `[LJ-1.504]`'s `someEnvDef-gap` from the frame hypothesis
`arNumC`, then applying its `gap-suffices`.** Land nothing in `src/`.

**EVERY PIECE IS DELIVERED AND GREEN. THIS TASK JOINS THEM.**

1. **`[LJ-1.504]` proved the gap sufficient.** `gap-suffices`
   (`agents/tasks/LJ-1-504/Probe504.agda:133-138`) takes `someEnvDef-gap` and
   returns exactly this obligation, already parameterised over the five free
   slots. It is GO on that term; its STOP was only that the gap was unpaid.
2. **`[LJ-1.500]` is GO and shows how to pay a gap of this shape.** Its
   `module Num` (`agents/tasks/LJ-1-500/Probe500.agda:225-239`) takes ONE frame
   hypothesis,
   `arNumC : (c : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩ → ⟨ (c ∷ γ) ⊨ arityNumAtL zero ⟩`,
   and derives the numeral truncation from it.
3. **`[LJ-1.506]` proved the truncation is FALSE without such a hypothesis.**
   `bare-C-is-not-a-theorem` (`agents/tasks/LJ-1-506/Probe506.agda:143-150`) is a
   machine-checked refutation at a bare `C : S`. **So a hypothesis about slot two
   is REQUIRED, and this is the one to use.**

**THE MATHEMATICIAN HAS RULED `arNumC` AND NOT `[LJ-1.506]`'s EQUATION.**
`[LJ-1.506]` proposed naming slot two by `fst (lookup C γ') ≡ fst (AllCodes A)`
and said plainly that it changes `codesK`'s type at 25 sites, which is a record
redesign and not a coder's call. **The ruling is the weaker hypothesis**, for the
same reason the weakest sufficient gate won at `[LJ-1.503]`: `arNumC` is already
built and GO at both readers, it changes NO field type, and it leaves slot two
free for whatever `[LJ-1.505]` settles. **`arityNumAtL` is the tree's own
predicate** (`src/L/Choice/Faithful.lagda.md:64`) and the record's own comment
already names it for this purpose (`src/L/Condensation/TwelveAgree.lagda.md:304`).

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-507/Probe507.agda::someEnv-at-frame"]

## SCOPE (write)
- agents/tasks/LJ-1-507/Probe507.agda
- agents/tasks/LJ-1-507/lj-1.507-report.md
- agents/tasks/LJ-1-507/review-of-someEnv-at-frame.md
- agents/tasks/LJ-1-507/runs/

## PREMISES

1. `[LJ-1.504]`'s `gap-suffices` returns this obligation from the gap. Basis: agents/tasks/LJ-1-504/Probe504.agda:133
2. Its report calls the gap the whole remaining distance. Basis: agents/tasks/LJ-1-504/lj-1.504-report.md:46
3. `[LJ-1.500]` is GO on both reader fields. Basis: agents/tasks/LJ-1-500/lj-1.500-report.md:145
4. Its `module Num` takes the frame hypothesis and derives the truncation. Basis: agents/tasks/LJ-1-500/Probe500.agda:225
5. Its derivation of the truncation is `codesK-num`. Basis: agents/tasks/LJ-1-500/Probe500.agda:230
6. `[LJ-1.506]` is GO and refuted the truncation at a bare slot. Basis: agents/tasks/LJ-1-506/Probe506.agda:143
7. It derived the truncation once the set is named. Basis: agents/tasks/LJ-1-506/Probe506.agda:79
8. `arityNumAtL` is a delivered predicate of the tree. Basis: src/L/Choice/Faithful.lagda.md:64
9. The record's own comment names it for the arity component. Basis: src/L/Condensation/TwelveAgree.lagda.md:304
10. `someEnvDef` is the type the field states. Basis: src/L/Condensation/LowerAgree.lagda.md:52
11. `KValue` binds the carrier and the stage. Basis: src/L/Condensation.lagda.md:7380
12. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
13. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
14. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**`someEnv` HAS COST MORE DISPATCHES THAN ANY OTHER FIELD IN THIS RECORD.**
`[LJ-1.488]` priced two repairs, `[LJ-1.491]` found the gate a home,
`[LJ-1.493]` built the term at a probe frame, `[LJ-1.496]` measured that the
landing chain is stage-free, `[LJ-1.503]` settled the gate, `[LJ-1.504]` closed
two of three differences and proved the third sufficient, and `[LJ-1.506]` proved
that third derivable under a hypothesis. **Nothing is unmeasured. This is the
join.**

## WHAT IS MISSING

The join, and nothing else.

## THE REASONING

**D-10, BEFORE ANY AGDA.** `[LJ-1.500]`'s `arNumC` is stated at ITS frame and
`[LJ-1.504]`'s `gap-suffices` is stated at `gam' g1 g2 g3 g4 g5`. **Say at
`file:line` whether the two frames agree, slot for slot.** If `arNumC` cannot be
stated at 504's frame, name the difference and STOP: that would mean the two
green results do not compose, which is worth knowing before anything is built on
either.

**REBUILD BOTH, DO NOT IMPORT.** `[LJ-1.500]`'s `Num` and `[LJ-1.504]`'s
`gap-suffices` are both probe-local. Rebuild what you need at their delivered
types. Do not import a probe.

**DO NOT USE `[LJ-1.506]`'s EQUATION AND DO NOT NAME `AllCodes`.** The
mathematician has ruled the weaker hypothesis and the reason is that the equation
would change 25 field types. If you find `arNumC` insufficient, that is the
finding and the ruling reopens.

**DO NOT POSTULATE `arNumC`.** It is a frame HYPOTHESIS: take it in the
telescope, exactly as `[LJ-1.500]` does. A postulate would make the term
worthless.

**REQUIRED REPORT SECTION `## WHAT someEnv COST IN THE END`.** Name every
predecessor whose delivered term you used, at `file:line`, and say in one
sentence what remains between this and a `TFacts` value. **Do not build that
value**: fifty-nine positions are out of scope and AD12 gives this brief one
obligation.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 200 lines in the probe, of which the obligation is
about 40 and the rest is the two rebuilt frames. BASIS: `[LJ-1.504]` and
`[LJ-1.500]` each rebuilt one of them in a comparable file. Comparables are of
SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is the agreement of the two frames, because each green result was measured at
its own and nobody has put them side by side.

    arNumC-at-504-frame :
      (c : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) (gam' g1 g2 g3 g4 g5)) ⟩
      → ⟨ (c ∷ gam' g1 g2 g3 g4 g5) ⊨ arityNumAtL zero ⟩

**Write it FIRST, as a type in 504's frame, and typecheck it ALONE.** If it does
not form, the two results do not compose and the task stops at its cheapest
point with that as the finding.

ESTIMATE for W3: about 15 lines and under 30 seconds. **Do not fund it against
`[LJ-1.500]`'s 3.16 s**: that measured two reader fields and this states one
hypothesis at a different frame.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS THE FIELD THAT COST THE MOST**, and leaves the record with no field
whose supplier is unknown.

**A NO-GO SAYS TWO GREEN RESULTS DO NOT COMPOSE AT ONE FRAME**, which would send
the frame decision back to the mathematician with a named difference rather than
a suspicion.

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
  changed_files_none = ["agents/tasks/LJ-1-507/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-507/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-507/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-507/Probe507.agda"]
  changed_files_none = ["agents/tasks/LJ-1-507/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-507/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 224.028)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 210.654)
- CANDIDATE archive/dev/JOURNAL.md  (score 190.194)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 172.549)
- CANDIDATE dev/ARCHIVE.md  (score 162.662)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/truncation-and-selection.md  (score 66.154)
- CANDIDATE dev/literature/devlin-II5.md  (score 59.269)
- CANDIDATE dev/literature/digest.md  (score 39.426)
- CANDIDATE dev/literature/geology.md  (score 38.990)
- CANDIDATE dev/literature/terms-2026-08.md  (score 38.457)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
