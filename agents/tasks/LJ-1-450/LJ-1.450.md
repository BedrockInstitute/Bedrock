# LJ-1.450: the environment the condensation frame has never been given

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-450/Probe450.agda`:

    someEnv-at-K : someEnvDef {3} iK Kenv

where `someEnvDef` is `src/L/Condensation/LowerAgree.lagda.md:52-58`, and
`Kenv`, `iK` are the fourteen-slot frame `KValue` delivers at a REAL bound
(`src/L/Condensation.lagda.md:7387-7409`). Land nothing in `src/`.

**IF THE INDEX CONVENTIONS DO NOT MEET, SAY SO AND STOP.** That is W3 below and
it is the whole risk of this task. State the obligation at whatever `n` and
whatever index the two sides actually share, and report the arithmetic you had
to write. **Do not invent a re-layout of `Kenv` to make it fit**: if a re-layout
is needed, name it as a type in `## WHAT IS LEFT` and stop.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-450/Probe450.agda::someEnv-at-K"]

## SCOPE (write)
- agents/tasks/LJ-1-450/Probe450.agda
- agents/tasks/LJ-1-450/lj-1.450-report.md
- agents/tasks/LJ-1-450/review-of-someEnv-at-K.md
- agents/tasks/LJ-1-450/runs/

## PREMISES

1. `TFacts` is the record the twelve-row agreement takes, and it has 55 fields. Basis: src/L/Condensation/TwelveAgree.lagda.md:129
2. `someEnv` is one of those fields. Basis: src/L/Condensation/TwelveAgree.lagda.md:289
3. **`TFacts` HAS NO INHABITANT.** `grep -rn "TFacts" src agents` returns the definition, one parameter, one `open`, and one comment in a probe, and nothing else. Basis: src/L/Condensation/TwelveAgree.lagda.md:342
4. `KValue` inhabits the SMALLER record `KFacts` at a real bound, with every field a term and no hole. Basis: src/L/Condensation.lagda.md:7410
5. `[LJ-1.113]` classified the difference between the two records: 28 facts need new content, 1 is derivable, 0 unknown. Basis: agents/tasks/LJ-1-113/lj-1.113-report.md:8
6. It names `someEnv` as THE widest unmeasured term, the only one whose supplier is a construction and not a closure, and it names the probe. Basis: agents/tasks/LJ-1-113/lj-1.113-report.md:147
7. It prices the whole 28 at about 250 in-fence lines, and calls the figure a hypothesis. Basis: agents/tasks/LJ-1-113/lj-1.113-report.md:135
8. The twelve-row agreement says in the tree what it still needs: the frame instantiated at a real `K`. Basis: src/L/Condensation/TwelveAgree.lagda.md:524
9. The consumer of that agreement is live and its two parameters are unsupplied. Basis: src/L/Condensation.lagda.md:6971
10. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
11. A measured cure does not transfer by analogy; re-measure it at its own site. Basis: dev/LESSONS.md:3752
12. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THE AGREEMENT STACK IS COMPLETE AS AN ABSTRACT FRAME AND IT FEEDS NOTHING.**
`src/L/Condensation/TwelveAgree.lagda.md` is 538 lines and delivers
`twelve-out` (`:527`) and `twelve-back` (`:533`). **No file imports it**:
`grep -rln "import L.Condensation.TwelveAgree" src` returns nothing outside the
catalog. Its own comment says why (`:520-526`): it exports the consumer's TYPE
and discharges nothing, because supplying `SatGraphAgree` still needs the frame
instantiated at a real `K`.

**THE REAL `K` EXISTS.** `KValue` (`src/L/Condensation.lagda.md:7380-7434`)
builds the fourteen-slot environment from a limit bound and a stage below it,
and inhabits `KFacts` with terms: `numK0` through `numK11` from `B.num∈λ`,
`pairK` from `B.prʟ∈λ`, `carrierK` from `Lset-mono`, `arityK` from
`B.trans∈λ` (`:7411-7427`).

**SO THE CHAIN IS SHORT AND ITS ONE BREAK IS NAMED.** `KFacts` at a real K is
delivered. `TFacts` at that same K is not. `[LJ-1.113]` measured the difference
and stopped, by its own abort criterion (`lj-1.113-report.md:17`).

## WHAT IS MISSING

An inhabitant of `TFacts`. This task builds the ONE field that is a
construction. It does not build the other 27.

## THE REASONING

**WHY THIS FIELD AND NOT ANOTHER.** `[LJ-1.113]` split the 28 into three
shapes (`lj-1.113-report.md:61-66`): 25 satisfier-in-K closures, 2 slot
equalities the consumer's own site supplies, and 1 environment-existence
construction. **The 25 share one pattern and the 1 does not.** A closure lemma
reads a satisfaction premise and returns a membership; `someEnv` must BUILD an
environment in K. If the construction fails, the 250-line price fails with it,
whatever the 25 cost.

**D-10, BEFORE ANY AGDA.** Open `src/L/Condensation/LowerAgree.lagda.md:52-58`
and quote `someEnvDef` in full. Open `src/L/Condensation.lagda.md:7387-7409`
and quote `Kenv` and the fourteen index names. **Write both index conventions
down side by side before you write a term**: `TFacts` reads its frame at
`lookup (suc (suc (suc (suc (suc (suc X))))) ) γ'` over `S ^ (11 + n)`
(`TwelveAgree.lagda.md:133`), and `KValue` reads `Kenv : S ^ 14` at bare `Fin 14`
indices (`Condensation.lagda.md:7396-7409`). **Say in one line whether an
`n` exists that makes the two agree, and give the arithmetic.**

**THE SHAPE.**

1. Import `L.Condensation` and `L.Condensation.LowerAgree` from `src/`. Do not
   import a probe and do not copy `KValue`'s body.
2. Do W3 first and report it before writing the obligation.
3. Build `someEnv-at-K` from the model's own environment constructors and the
   bound's closure facts, which `KValue` already has in scope through
   `module B = Bound lam ordλ succλ ∅∈λ` (`Condensation.lagda.md:7385`).

**DO NOT INHABIT THE OTHER 27 AND DO NOT WRITE A `TFacts` RECORD.** One field.
AD12 gives this brief one obligation.

**DO NOT POSTULATE AND DO NOT WEAKEN.** If `someEnvDef` cannot be inhabited at
this frame, that is a NO-GO and the obstruction file is the deliverable. **Do
not add a hypothesis to make it close**: a telescope that grows to close a case
is the shape audit findings F1 and F3 measured
(`dev/pod/audit-2026-08-20.md:34`).

**REQUIRED REPORT SECTION `## WHAT THE 27 NOW COST`.** `[LJ-1.113]` priced the
28 at about 250 lines and called the figure a hypothesis
(`lj-1.113-report.md:143-146`). You will have measured one of them. **Give the
measured line count and wall time for `someEnv-at-K`, then say whether 113's
figure still stands, and do not re-price the 25 closures from this one
construction**: they are a different shape and C-42 forbids the transfer
(`dev/LESSONS.md:3752`).

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 130 lines in the probe, of which the obligation is
about 40. BASIS: `KValue` is 55 lines including its fourteen index names
(`src/L/Condensation.lagda.md:7380-7434`), and this file restates that frame and
adds one construction. `[LJ-1.113]:135` prices all 28 at about 250 lines and
names this one as the only construction. Comparables are of SHAPE, and nothing
may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is whether the two frames meet at all.

    frame-meets : TFacts {3} i0' i1' i2' i3' i4' i5' i6' i7' i8' i9' i10' i11'
                         t0' t1' iK' Kenv → Type
    frame-meets _ = Unit

**Do not write that line. Write the SMALLER thing it stands for**: take the
twelve `tagEq` fields and the twelve `numK` fields of `TFacts`
(`TwelveAgree.lagda.md:133-156`), state them as a Sigma at `KValue`'s `Kenv`,
and inhabit them from `KValue.facts` (`Condensation.lagda.md:7411`).
Typecheck it ALONE with the obligation omitted.

**Those 24 fields are the ones `KFacts` already has, so if they do not transfer
the break is the LAYOUT and not the mathematics.** The elaborator's error at
`file:line` IS the finding, and it is worth more than the obligation: it says
the agreement stack and the real K were built to two conventions and nobody has
ever put them in one file.

ESTIMATE for W3: about 30 lines and under 5 seconds. BASIS: the 24 fields are
`refl` and `B.num∈λ` applications in `KValue` (`Condensation.lagda.md:7413-7419`).
If it costs more, the layout is the reason and the report says so.

Report the median wall time and the peak RSS over three forced rechecks at the
pane's caliber, for W3 alone and for the full file.

## WHAT GO AND NO-GO EACH EARN

**A GO OPENS THE CONDENSATION FRONT.** It puts the first `TFacts` field in the
tree at a real K, and it turns `[LJ-1.113]`'s 250-line hypothesis into a figure
with one measured member.

**A NO-GO IS WORTH MORE THAN THE GO.** The likely NO-GO is the W3 one: the
frames do not meet. That is a defect between two live chapters, it has stood
since `[LJ-1.113]`, and every later plan for the condensation lemma rests on it.

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
# A D-10 STOP RUNS NO AGDA, SO IT EXITS 0 AND MATCHES NO exit_code 42 BRANCH.
# MEASURED 2026-08-21: this row fired on `[LJ-1.448]` and routed it to a critic
# (dev/pod/transitions/2026-08.jsonl:915), where `[LJ-1.440]` parked no-match
# seven times without one. A stated NO-GO is the critic's input, never a close.
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-450/review-of-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-450/Probe450.agda"]
  changed_files_none = ["agents/tasks/LJ-1-450/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-450/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 272.646)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 235.621)
- CANDIDATE archive/dev/JOURNAL.md  (score 229.281)
- CANDIDATE dev/ARCHIVE.md  (score 192.555)
- CANDIDATE archive/dev/DECISIONS-archived.md  (score 175.855)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/digest.md  (score 59.870)
- CANDIDATE dev/literature/devlin-II5.md  (score 58.944)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 56.963)
- CANDIDATE dev/literature/level-formula-slot-roles.md  (score 36.456)
- CANDIDATE dev/literature/geology.md  (score 35.765)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
