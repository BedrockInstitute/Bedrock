# LJ-1.511: someEnvDef with the truncation in its own type

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-511/Probe511.agda`:

    someEnv-at-corrected-def :
        (g1 g2 g3 g4 g5 : S) → someEnvDef' {9} KV.iK (gam' g1 g2 g3 g4 g5)

where `someEnvDef'` is `someEnvDef` **with `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁`
added to its own hypotheses**, stated locally in the probe. Land nothing in
`src/`.

**`[LJ-1.507]` IS A CRITIC-UPHELD NO-GO AND IT REFUTED A CHAIN, NOT A STEP.**
`someEnvDef-gap` has **no inhabitant at `[LJ-1.504]`'s own frame**, machine
checked under `--safe` (`agents/tasks/LJ-1-507/Probe507.agda:257-268`). So
`[LJ-1.504]`'s `gap-suffices` is a true implication out of an empty antecedent
and it inhabits nothing. **`[LJ-1.504]`'s claim that the truncation was proved
sufficient is VACUOUS, and no brief may cite it as sufficiency again.**

**THE MATHEMATICIAN'S RULING HAS CHANGED AND THIS BRIEF CARRIES THE CHANGE.**
`[LJ-1.507]` says in one sentence what remains: **`someEnvDef` has to carry the
numeral truncation in its own type before `someEnv` can be filled at all.** That
is the half of `[LJ-1.488]`'s Repair A that I ruled against at `[LJ-1.493]`, and
the refutation forces it back.

**THE NEW RULING IS A SPLIT THAT NEITHER REPAIR PROPOSED.** The truncation goes
IN, because `[LJ-1.488]` measured that it can: "The truncation can: it mentions
only `ar`" (`agents/tasks/LJ-1-488/lj-1.488-report.md:279`). The gate stays OUT,
because the same passage measured that `⟨ ω ∈ sucV gam ⟩` "cannot be stated there
without adding `gam` as a parameter" (`:277-279`), and P-l forbids putting that
presentation in a tower-generic type.

**AND THIS HALF IS LANDABLE WHERE THE OTHER WAS NOT.** `[LJ-1.496]` measured that
the whole `PropAgree` to `AbstractFrame` chain binds no `V ℓ` stage
(`agents/tasks/LJ-1-496/lj-1.496-report.md:78-82`). **The truncation needs no
stage**: it mentions only `ar`. So that wall does not block it.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-511/Probe511.agda::someEnv-at-corrected-def"]

## SCOPE (write)
- agents/tasks/LJ-1-511/Probe511.agda
- agents/tasks/LJ-1-511/lj-1.511-report.md
- agents/tasks/LJ-1-511/review-of-someEnv-at-corrected-def.md
- agents/tasks/LJ-1-511/runs/

## PREMISES

1. `[LJ-1.507]` is a critic-upheld NO-GO and its gap is FALSE, not unpaid. Basis: agents/tasks/LJ-1-507/lj-1.507-report.md:3
2. Its refutation is machine checked. Basis: agents/tasks/LJ-1-507/Probe507.agda:257
3. Its one sentence names the cure: the truncation must sit in the definition's type. Basis: agents/tasks/LJ-1-507/review-of-someEnv-at-frame.md:8
4. `[LJ-1.488]` measured that the truncation CAN be stated there. Basis: agents/tasks/LJ-1-488/lj-1.488-report.md:279
5. It measured that the gate CANNOT, without adding `gam` as a parameter. Basis: agents/tasks/LJ-1-488/lj-1.488-report.md:277
6. `someEnvDef` is the type to correct. Basis: src/L/Condensation/LowerAgree.lagda.md:52
7. `[LJ-1.496]` measured that the chain binds no stage. Basis: agents/tasks/LJ-1-496/lj-1.496-report.md:78
8. `[LJ-1.503]` settled the gate at `SupplyEnv`'s own form. Basis: agents/tasks/LJ-1-503/lj-1.503-report.md:22
9. `[LJ-1.500]` is GO and derives the truncation from a frame hypothesis. Basis: agents/tasks/LJ-1-500/Probe500.agda:230
10. `SupplyEnv.someEnv` is the delivered supplier. Basis: src/L/Coding/EnvSupply.lagda.md:417
11. `KValue` binds the carrier and the stage. Basis: src/L/Condensation.lagda.md:7380
12. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
13. A measured cure does not transfer by analogy. Basis: AGENTS.md:45
14. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**EIGHT DISPATCHES HAVE MEASURED THIS ONE FIELD AND THE LAST OF THEM REFUTED THE
ROUTE THE OTHER SEVEN BUILT TOWARD.** What survives is solid: the supplier
exists, the gate is settled, the truncation is derivable under a frame
hypothesis, and the target type is now known to be wrong as written.

## WHAT IS MISSING

The corrected type, and a term at it.

## THE REASONING

**D-10, BEFORE ANY AGDA.** State `someEnvDef'` in the probe, copying
`src/L/Condensation/LowerAgree.lagda.md:52-58` and adding ONE hypothesis. **Say
at `file:line` what you copied and what you added.** Then check the thing
`[LJ-1.507]` checked: **is the corrected statement non-vacuous at this frame?**
If its antecedents are again unsatisfiable, STOP and say so: a second empty
antecedent would mean the field's shape is wrong in a deeper way than one
hypothesis.

**DO NOT CITE `[LJ-1.504]`'s `gap-suffices` AS SUFFICIENCY.** It is a true
implication out of an empty antecedent. You may rebuild its shape; you may not
use it as evidence that anything is enough.

**DO NOT EDIT `src/` AND DO NOT ADD `gam` TO `someEnvDef'`.** The gate stays
where `SupplyEnv` states it, by the ruling at `[LJ-1.503]`. Adding `gam` would
put a presentation in a tower-generic type and P-l forbids it.

**DO NOT POSTULATE THE TRUNCATION.** It is a hypothesis of the corrected type:
take it, and use it exactly as `[LJ-1.500]` uses `arNumC`'s output.

**REQUIRED REPORT SECTION `## IS THE CORRECTED TYPE NON-VACUOUS`.** Exhibit one
inhabitant of its antecedents at this frame, or say NONE. **This section is the
deliverable even if the obligation is not built**, because `[LJ-1.507]` proved
that a green term against an empty antecedent is worth nothing.

**REQUIRED REPORT SECTION `## WHAT THE LANDING WOULD COST`.** Name the sites that
would change if this correction landed in `src/`, at `file:line`, and say for
each whether the change is a type or a call. **Do not land it.**

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 190 lines in the probe, of which the obligation is
about 45. BASIS: `[LJ-1.507]` rebuilt this frame, the gap and a refutation in a
comparable file. Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is non-vacuity, because `[LJ-1.507]` proved that this is the thing that was
never checked and that its absence made three dispatches worthless.

    antecedents-inhabited : (one witness of someEnvDef' 's hypotheses at this frame)

**Write it FIRST, before the obligation, and typecheck it ALONE.** If the
corrected type is again vacuous, nothing built on it means anything, and the task
stops at its cheapest point with the strongest finding available.

ESTIMATE for W3: about 25 lines and under 40 seconds. **Do not fund it against
`[LJ-1.507]`'s refutation**: that built a counterexample and this builds a
witness.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO PAYS THE FIELD THAT HAS COST THE MOST** and turns the correction into a
landing the mathematician can price.

**A SECOND EMPTY ANTECEDENT SAYS THE FIELD'S SHAPE IS WRONG BEYOND ONE
HYPOTHESIS**, which would send `someEnvDef` back to its author's intent rather
than to another repair, and that is worth more than a ninth attempt at the same
shape.

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
  changed_files_none = ["agents/tasks/LJ-1-511/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-511/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-511/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-511/Probe511.agda"]
  changed_files_none = ["agents/tasks/LJ-1-511/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-511/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 235.505)
- CANDIDATE archive/dev/JOURNAL.md  (score 197.273)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 194.229)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 164.177)
- CANDIDATE dev/ARCHIVE.md  (score 153.774)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/digest.md  (score 66.266)
- CANDIDATE dev/literature/devlin-II5.md  (score 64.274)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 61.216)
- CANDIDATE dev/literature/geology.md  (score 43.639)
- CANDIDATE dev/literature/glossary-review-2026-08.md  (score 39.344)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
