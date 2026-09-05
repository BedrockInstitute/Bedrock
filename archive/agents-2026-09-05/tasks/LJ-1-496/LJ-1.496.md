# LJ-1.496: land Repair B, all five site groups, in one commit

## HEAD
head_slot: coder
machine: exclusive

## THE OBLIGATION

Land ONE new term in `src/L/Condensation.lagda.md`:

    someEnvK : (the environment SupplyEnv supplies, at PropAgree's frame)

**and use it at the `:3515` call site, then retire the field it replaces and
every site that passes it.** This is Repair B, landed. `[LJ-1.493]` built the
term in a probe and is GO. You promote it, and the deletions follow in the SAME
commit.

**`[LJ-1.493]` IS THE PAD AND IT IS COMMITTED** (`018dcc8`, row
`task-lj-1-493-go`). Its `someEnv-inlined` typechecks at
`agents/tasks/LJ-1-493/Probe493.agda:139-184`, median 4.53 s. It opens
`SupplyEnv` at the `KValue` telescope plus `⟨ ω ∈ sucV gam ⟩` (`:109-112`) and
calls `SE.someEnv` (`:169`). **Take that construction. Do not re-derive it.**

**THE FIVE GROUPS, FROM `[LJ-1.488]` AND RE-CHECKED BY `[LJ-1.493]`
(`agents/tasks/LJ-1-493/lj-1.493-report.md:233-252`):**

| group | sites | kind |
|---|---|---|
| 1 | `src/L/Condensation.lagda.md:3515` | use the new term; `arNum` is bound at `:3509` |
| 2 | `src/L/Condensation.lagda.md:3285-3320` | `PropAgree` takes `lam`, `gam`, `ω∈γ` and opens `SupplyEnv` |
| 3 | `src/L/Condensation.lagda.md:3317`, `:3569`, `:3624` | the `someEnv` parameter goes |
| 4 | `src/L/Condensation/LowerAgree.lagda.md:52-58`, `:218`, `:273`, `:279` | retire `someEnvDef` and `LFacts.someEnv` |
| 5 | `src/L/Condensation/TwelveAgree.lagda.md:289`, `:442` | delete `TFacts.someEnv` and its fill |

**THE CHAIN IS FIVE SITES IN TWO CHAPTERS AND I MEASURED IT.** `PropAgree` is
used at `src/L/Condensation.lagda.md:3575` and `:3630` only, by `AndAgree` and
`OrAgree`; those two are used at `src/L/Condensation/LowerAgree.lagda.md:269` and
`:275` only. **Nothing else in `src/` names any of the three.**

**DO ALL FIVE GROUPS IN ONE PASS.** A split leaves `PropAgree` carrying both the
new telescope and the dead parameter, which is a state nobody wants and which
costs the same five sites twice.

## OBLIGATION NAMES
obligations = ["src/L/Condensation.lagda.md::someEnvK"]

## SCOPE (write)
- src/L/Condensation.lagda.md
- src/L/Condensation/LowerAgree.lagda.md
- src/L/Condensation/TwelveAgree.lagda.md
- agents/tasks/LJ-1-496/lj-1.496-report.md
- agents/tasks/LJ-1-496/review-of-someEnvK.md
- agents/tasks/LJ-1-496/runs/

## PREMISES

1. `[LJ-1.493]` is GO and its term typechecks at the real frame. Basis: agents/tasks/LJ-1-493/lj-1.493-report.md:72
2. It opens `SupplyEnv` at the `KValue` telescope and calls `SE.someEnv`. Basis: agents/tasks/LJ-1-493/Probe493.agda:169
3. Its W3 found the frame reachable: `c∈` is a binder and `C` is a parameter. Basis: agents/tasks/LJ-1-493/lj-1.493-report.md:74
4. The five groups and their kinds are re-checked in that report. Basis: agents/tasks/LJ-1-493/lj-1.493-report.md:233
5. The call site to replace is the `:3515` binding. Basis: src/L/Condensation.lagda.md:3515
6. `arNum` is already bound above it. Basis: src/L/Condensation.lagda.md:3509
7. `PropAgree` is the module to re-parameterise. Basis: src/L/Condensation.lagda.md:3285
8. `AndAgree` uses it. Basis: src/L/Condensation.lagda.md:3575
9. `OrAgree` uses it. Basis: src/L/Condensation.lagda.md:3630
10. `LowerAgree` instantiates both, and nothing else does. Basis: src/L/Condensation/LowerAgree.lagda.md:269
11. The gate to take is the one `SupplyEnv` states. Basis: src/L/Coding/EnvSupply.lagda.md:111
12. `TFacts.someEnv` is the field that goes. Basis: src/L/Condensation/TwelveAgree.lagda.md:289
13. `make check` is the gate before any commit. Basis: AGENTS.md:75
14. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34

## WHAT IS DELIVERED ALREADY

**TWELVE DISPATCHES REACHED THIS FIELD AND THE TWELFTH BUILT ITS TERM.**
`[LJ-1.488]` priced the two repairs, `[LJ-1.491]` gave the gate a home at
`KValue` with no landed consumer losing an instance, and `[LJ-1.493]` inhabited
the replacement at the real frame. **Nothing about this landing is unmeasured
except the landing.**

## WHAT IS MISSING

The edits.

## THE REASONING

**D-10, BEFORE ANY AGDA.** `[LJ-1.493]` measured a PROBE frame that rebuilds
`:3515`'s. Open the real one and say at `file:line` whether `lam`, `gam` and the
gate can reach `PropAgree` from where it is instantiated. **If `LowerAgree:269`
cannot supply them, STOP AND SAY SO**: that would mean Repair B is not landable
at this chain and the mathematician must re-open the choice against Repair A.

**THE RATIO BAR IS LIVE AND THIS IS A `.lagda.md` MASTER.** The bar is 0.0123
seconds per in-fence line and a green return at or above it escalates. Design for
it. The deletions help you: group 4 and group 5 remove lines from the divisor's
chapters, so measure before and after and report both.

**DELETE, DO NOT COMMENT OUT.** A retired definition goes, and `archive/` is for
a retired MODULE, not for a dead fragment. If a deletion breaks a consumer this
brief did not name, that consumer is the finding: name it at `file:line` and
STOP rather than widening the edit.

**RUN THE INDIVIDUAL CHECKS AS YOU GO AND `make check` BEFORE YOU REPORT.**
Never commit and never push. The program commits, by explicit path.

**REQUIRED REPORT SECTION `## THE FIVE GROUPS, LANDED.`** One row per group with
its final `file:line`, what changed, and the line delta. **If a group did not
land, say which and why, and do not claim Repair B.**

**REQUIRED REPORT SECTION `## WHAT TFACTS OWES NOW.`** Give the field count of
`TFacts` after this lands, measured, and name `someEnv` as gone. **Do not price
the remaining fields.**

ESTIMATE for the Agda: about 60 changed lines across the three chapters, of which
the new term is about 25 and the rest is telescope and deletion. BASIS:
`[LJ-1.493]`'s probe body is 45 lines for the construction, and the chain is five
sites. Comparables are of SHAPE and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is `PropAgree`'s new telescope reaching its two callers, because `[LJ-1.493]`
measured the construction and never measured the chain.

    -- AndAgree and OrAgree, instantiated with the three new arguments,
    -- from LowerAgree:269 and :275

**Do this FIRST, with the deletions omitted and the old parameter still in
place, and typecheck the two chapters ALONE.** If the three arguments cannot
reach `PropAgree` from `LowerAgree`, the landing stops at its cheapest point and
the old code is still whole.

ESTIMATE for W3: about 20 changed lines and under 120 seconds for the two
chapters. **Do not fund it against `[LJ-1.493]`'s 4.53 s**: that was one probe
file and this is two masters.

Report the median wall time and peak RSS over three forced rechecks, for W3
alone and for the full three chapters.

## WHAT GO AND NO-GO EACH EARN

**A GO CLOSES A FIELD THAT TOOK TWELVE DISPATCHES** and removes a record field,
a definition and four passing sites from three landed chapters.

**A NO-GO AT W3 SAYS REPAIR B IS NOT LANDABLE AT THIS CHAIN**, which re-opens the
choice against Repair A and is worth knowing before more work rests on it.

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
  seconds_per_line_max = 0.0123

[[branch]]
# BOTH EXCLUSIONS DELIBERATE. No delta key: measured on LJ-1.453, a closing
# record can carry delta 0 and the row must still match.
id = "ratio-bar"
priority = 11
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 0
  changed_files_none = ["agents/tasks/LJ-1-496/review-of-LJ-*-*.md"]
  heap_wall = false
  seconds_per_line_min = 0.0123

[[branch]]
id = "accept-failed"
priority = 14
action = "escalate"
head_slot = "coder_adversarial"

  [branch.when]
  exit_code = 1
  changed_files_none = ["agents/tasks/LJ-1-496/review-of-LJ-*-*.md"]

[[branch]]
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-496/review-of-*.md"]
  changed_files_none = ["agents/tasks/LJ-1-496/review-of-LJ-*-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["src/L/Condensation.lagda.md"]
  changed_files_none = ["agents/tasks/LJ-1-496/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-496/review-of-*.md"]

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

MANDATORY for kind `build` (writes a master under src/. The heaviest bundle, because a build is where seconds and lines are actually spent.):

- **P-h. Definability walks are module-parameterized, never function-parameterized**
  **Rule:** A definability walk (the `defSet≡` extensionality of an InL-idiom constructibility lemma) takes its set arguments as parameters of a module, not of a function, and those parameters stay ABSTRACT through the walk: the formulas and the readers never mention a concrete `sett` body (`slice`, `satSet`, a stage over them); the instantiation at real sets happens only at the lemma-assembly le...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:200
- **P-k. A read lemma is stated where its consumers use it, not where its proof ends**
  **The law.** When a lemma exists so that consumers can rewrite with it, its stated right-hand side must be **the form the consumers actually need**, not the form the proof happened to reach. If it stops one layer early, every consumer re-normalizes the missing layer, and the same conversion is paid once per consumer instead of once in total. **Absorb the last layer into the lemma and seal it**,...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2453
- **P-l. A statement may be ABOUT a concrete stage without dragging that stage's PRESENTATION into its type**
  **The law.** Being about a concrete position is not what costs. Naming a transparent construction in a statement's TYPE is. If the tower's stage values are `opaque` upstream, a theorem may quantify over, hypothesize about and conclude at `Sset ω` freely, because the stage is an ATOM to the elaborator and nothing unfolds. If instead the type mentions a transparent presentation, such as `⟪ sucV (...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2357
- **P-m. The check-cost rate is a content-class certificate, and instantiation is the expensive class**
  **Rule:** Seconds per line identify a block's CONTENT CLASS before any profile is run, and line count alone predicts nothing. **Parameterized content**, whose definitions check at bound variables under a module telescope, checks near **0.01 s per line**. **Instantiation content**, which states object-language formulas at a concrete carrier, proves decodes that walk the satisfaction relation, an...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2512
- **P-n. Satisfaction content at a concrete carrier is a payable floor, not a defect**
  **Rule:** When a proof states object-language formulas at a CONCRETE carrier and proves their two-way decodes, the elaborator normalizes the carrier's presentation at every such definition, and **named branches with written types do not remove that cost**. I-5's cure applies to a missing type, not to this; if every hot branch already carries a written type, the remaining cost is the machinery a...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2535
- **R-35. Union representations are meta-poisoned; state memberships at small indices**
  **Rule:** Index or path extraction from the representation of a union of an open term (`⟪ ⋃ x ⟫`-level fiber extraction, `separation-ax` over a union) leaves unsolved metas or churns the presentation machinery; state the membership at the SMALL INDEX instead (an existential over `⟪ y ⟫` with the inclusion applied), and keep constructions at the stuck-member level.
  Full entry: dev/LESSONS.md:808
- **R-38. A consumer's alias of a transparent imported operation is a birth site**
  **Rule:** P-c extends one layer up: when a consumer names a composite of a TRANSPARENT imported operation (a derived op whose body reaches an imported sett/union tower), the consumer's alias is itself a birth site and must be sealed opaque with its spec inside, even though the imported operation was delivered transparent. Transparent-by-delivery kit operations (the Images F10 and the left/right...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:855
- **R-40. A deep successor-chain membership witness normalizes super-linearly; climb by small closures**
  **Rule:** An ordinal-membership premise stated at a deep iterated successor (`+ω-iter n`, a `sucV`-chain) forces the conversion checker to normalize the whole chain against the level's union representation, and the cost is super-linear in the depth. State the witness at a SHALLOW index and climb by the limit-ordinal successor closure (`limit-succ-mem`, `L.Rud.Hierarchy:455`), one step per line....
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:955
- **I-5. Inner-world truncation branches carry written types**
  **Rule:** In the inner world, every `PT.rec`/`PT.map` branch gets a named `where` function with a WRITTEN type; a branch whose type is left to inference re-elaborates the inner satisfaction machinery per constraint and reads as a conversion wall. The trap's target class is wider than the retiring stack recorded: it fires on equations between iterated Kuratowski pairs, not only on disjunctions o...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:1255
- **C-12. Agda runs under a hard heap cap; parallel writers under a quota**
  **Rule:** Every agda invocation runs under a GHC heap cap (`GHCRTS=-M<n>g`) so a runaway typecheck dies with a clean "Heap exhausted" exit instead of OOM-killing the machine; the orchestrator's audits run at `-M16g` and `make` exports a default. Sub-agent concurrency is TIERED (owner-widened 2026-08-02 once the caps and the watchdog were live): WIDE mode for routine batches, up to FOUR concurre...
  THIS IS AN EXCERPT. Full entry: dev/LESSONS.md:2135
- **D-10. Price the truth of a recorded residue before pricing its proof**
  **Rule:** A residue recorded under the wall protocol names a TARGET, and a target can be false; before dispatching a discharge batch, spend the five minutes checking the target's truth at the intended generality (a Tarskian or cardinality obstruction is the usual killer), and record the corrected target beside the original.
  Full entry: dev/LESSONS.md:1375
- **C-22. A dispatched agent writes its deliverable incrementally, never at the end**
  **Rule:** When an agent's deliverable is a file, the brief must require it WRITTEN EARLY as a skeleton and filled incrementally, saving after each answer lands. An agent that researches for its whole budget and leaves the writing to the end returns nothing when the budget runs out, and its research dies with it. A partial dossier is a real deliverable; an unwritten perfect one is not.
  Full entry: dev/LESSONS.md:2297

## ARCHIVE (program-generated, do not edit)

Corpus search over archive/src, archive/dev, archive/scripts, dev/ARCHIVE.md:
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 258.198)
- CANDIDATE archive/dev/JOURNAL.md  (score 196.193)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 187.553)
- CANDIDATE archive/dev/PLAN-archived.md  (score 141.827)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 139.818)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 46.329)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 43.594)
- CANDIDATE dev/literature/digest.md  (score 39.292)
- CANDIDATE dev/literature/terms-2026-08.md  (score 35.770)
- CANDIDATE dev/literature/geology.md  (score 25.077)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
