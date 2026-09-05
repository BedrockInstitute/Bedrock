# LJ-1.447: the descent split at BOTH least cardinals, and the residue as one type

## HEAD
head_slot: coder
machine: shared

## THE OBLIGATION

Build ONE term in `agents/tasks/LJ-1-447/Probe447.agda`:

    descent-both :
        (residue : (y : V ℓ) (oy : IsOrd y) → ⟨ ω ∈ˢ y ⟩
                 → ⟨ fst (κL (y , isL-ord y oy) oy) ∈ˢ y ⟩
                 → ⟨ fst (κC (y , isL-ord y oy) oy) ∈ˢ y ⟩)
      → (x : V ℓ) (ox : IsOrd x) → ⟨ ω ∈ˢ x ⟩
      → ((y : V ℓ) → ⟨ y ∈ˢ x ⟩ → IsOrd y → (⟨ y ∈ˢ ω ⟩ → Empty.⊥) → sq y)
      → sq x

The induction hypothesis is DATA and the conclusion is DATA. `κL` is the
sealed ambient least cardinal (`agents/tasks/LJ-1-437/Probe437.agda:90-107`).
`κC` is the coded selection (`agents/tasks/LJ-1-431/Probe431.agda:126-134`).
Land nothing in `src/`.

**READ FOUR REPORTS BEFORE ANY AGDA, AND STOP IF ANY VERDICT IS NOT `GO`:**
`agents/tasks/LJ-1-421/lj-1.421-report.md` (`:52`),
`agents/tasks/LJ-1-432/lj-1.432-report.md` (`:63`),
`agents/tasks/LJ-1-433/lj-1.433-report.md` (`:51`) and
`agents/tasks/LJ-1-406/lj-1.406-report.md` (`:13`). Quote each verdict line and
each delivered type before you write a line of Agda.

## OBLIGATION NAMES
obligations = ["agents/tasks/LJ-1-447/Probe447.agda::descent-both"]

## SCOPE (write)
- agents/tasks/LJ-1-447/Probe447.agda
- agents/tasks/LJ-1-447/lj-1.447-report.md
- agents/tasks/LJ-1-447/review-of-descent-both.md
- agents/tasks/LJ-1-447/runs/

## PREMISES

1. `[LJ-1.421]` is GO on the descent split at the AMBIENT least cardinal, with case 3 paid and case 4 needing the arrow as data. Basis: agents/tasks/LJ-1-421/lj-1.421-report.md:52
2. Its case 3 is `by-init`, and it spends `init-at-kappa` and `via-col-square` and no code. Basis: agents/tasks/LJ-1-421/Probe421.agda:246
3. `[LJ-1.432]` is GO on case 4 at the CODED least cardinal, where the arrow is data by construction. Basis: agents/tasks/LJ-1-432/lj-1.432-report.md:63
4. Its delivered type takes the membership as a hypothesis and the induction hypothesis as DATA. Basis: agents/tasks/LJ-1-432/Probe432.agda:155
5. `[LJ-1.433]` is GO: `Init x` fails when the ambient least cardinal of `x` is a proper member of `x`. Basis: agents/tasks/LJ-1-433/lj-1.433-report.md:51
6. `[LJ-1.406]` is GO on `init-at-kappa` at a generic L-element, with a TRUNCATED induction hypothesis. Basis: agents/tasks/LJ-1-406/lj-1.406-report.md:13
7. Both least cardinals are members of the successor of the carrier, so each split has exactly two cases. Basis: agents/tasks/LJ-1-437/Probe437.agda:98
8. The coded selection's own membership is one line from the selected index. Basis: agents/tasks/LJ-1-430/Probe430.agda:98
9. `via-col-square` turns `Init` into the pairing as DATA. Basis: src/L/Ordinal/SquareLaw.lagda.md:959
10. A predecessor taken as a hypothesis is the REPORT and never the brief. Basis: dev/pod/audit-2026-08-20.md:34
11. A refutation measures the site it names and never how far that site extends. Basis: dev/LESSONS.md:3752
12. The architecture is a CANDIDATE and only a measurement settles it. Basis: dev/pod/screen.toml:10
13. No mathematical prose is written until both trophies are proved in the tree. Basis: AGENTS.md:69

## WHAT IS DELIVERED ALREADY

**THE TWO ROUTES ARE DUAL AND EACH HAS ONE OPEN HALF.**

| route | case 3, `fst κ ≡ x` | case 4, `fst κ ∈ x` |
|---|---|---|
| AMBIENT `κL` | PAID (`Probe421.agda:246-250`) | needs the arrow as data, and `[LJ-1.422]` is NO-GO |
| CODED `κC` | open (`agents/tasks/LJ-1-432/lj-1.432-report.md:180`) | PAID (`Probe432.agda:155-168`) |

**NOBODY HAS SPLIT ON BOTH AT ONCE.** Every task since `[LJ-1.421]` chose one
cardinal and inherited that cardinal's open half.

## WHAT IS MISSING

The four-case split, and the ONE case that survives it.

## THE REASONING

**D-10, BEFORE ANY AGDA. WORK THE FOUR CASES OUT ON PAPER AND WRITE THEM IN
THE REPORT BEFORE YOU WRITE THE TERM.** Split first on the coded cardinal, then
on the ambient one inside the first branch.

1. `fst (κC a ox) ∈ x`. **PAID.** It is `[LJ-1.432]`'s `descent-case4-coded` at
   this `x`, and the induction hypothesis it wants is DATA, which this telescope
   supplies (`Probe432.agda:158-160`).
2. `fst (κC a ox) ≡ x` and `fst (κL a ox) ≡ x`. **PAID.** It is `[LJ-1.421]`'s
   `by-init`: `via-col-square` applied to `init-at-kappa`, then `subst sq`
   (`Probe421.agda:246-250`). Truncate the induction hypothesis with `∣_∣₁` at
   the call, exactly as `members` does (`Probe421.agda:241-245`).
3. `fst (κC a ox) ≡ x` and `fst (κL a ox) ∈ x`. **VACUOUS UNDER `residue`.**
   The hypothesis gives `fst (κC a ox) ∈ˢ x`; case 2's equation rewrites it to
   `⟨ x ∈ˢ x ⟩`; `∈-irrefl` closes it (`Probe437.agda:39` imports it).
4. There is no fourth case, because each cardinal lies in the successor of `x`
   and the successor split has two branches and no third.

**IF THAT ACCOUNT IS WRONG, THE FINDING IS THE ACCOUNT AND NOT THE TERM.** Say
so in the report at `file:line` and stop. Do not repair it by adding a
hypothesis: a telescope that grows to make a case close is the shape audit
findings F1 and F3 measured (`dev/pod/audit-2026-08-20.md:34`).

**THE SHAPE.**

1. Rebuild the five-projection ambient seal (`Probe437.agda:90-107`) and the
   coded selection (`Probe431.agda:100-134`), with `nonempty-coded` as a module
   hypothesis. Do not import a probe.
2. Take `init-at-kappa`, `descent-case4-coded` and `descent-data` as MODULE
   HYPOTHESES at the types their probes delivered. Do not rebuild their proofs
   and do not re-measure conjunct 4 of `Init`.
3. Do W3 first, then the obligation.

**`residue` IS A HYPOTHESIS AND IT IS NOT A CLAIM.** Nothing in this tree
proves it and nothing in this tree refutes it. **Do not inhabit it, do not
postulate it, and do not weaken it to a truncation.** DD9 says a new principle
is stated as a type.

**REQUIRED REPORT SECTION `## WHAT IS LEFT`.** State `residue` as a type, and
state in one sentence what it says in words: when the ambient least cardinal of
an infinite ordinal lies strictly below it, so does the coded one. Then say,
with both types at `file:line`, how it differs from `[LJ-1.441]`'s obligation,
which asks for a code AT the ambient least cardinal. **`residue` asks for a
code at SOME member and not at that one.** Say which of the two is the weaker
statement and give the evidence.

**DO NOT CLAIM THE CAMPAIGN CLOSES AND DO NOT CLAIM THE TROPHY.** A GO says the
descent runs on DATA under one named hypothesis. It does not run the band
induction, and it does not touch `src/Landmarks.lagda.md`.

**NEVER COMMIT AND NEVER PUSH.**

ESTIMATE for the Agda: about 190 lines in the probe, of which the obligation is
about 30. BASIS: `agents/tasks/LJ-1-432/Probe432.agda` is 168 lines and carries
the coded seal, the plumbing and one case of this split; `[LJ-1.421]`'s own
`splitOwn` is 3 lines over two paid cases (`Probe421.agda:260-263`).
Comparables are of SHAPE, and nothing may be funded against them.

## W3, THE WIDEST UNMEASURED TERM

It is whether the TWO SPLITS agree on one carrier, because the two cardinals
were built at two sites and no file has ever held both.

    both-in-suc :
        (x : V ℓ) (ox : IsOrd x) → ⟨ ω ∈ˢ x ⟩
      → ⟨ fst (κL (x , isL-ord x ox) ox) ∈ˢ sucV x ⟩
        × ⟨ fst (κC (x , isL-ord x ox) ox) ∈ˢ sucV x ⟩

**Write it FIRST, with the obligation omitted, and typecheck it ALONE.** The
left half is projection three of the ambient seal (`Probe437.agda:98-100`). The
right half is one line from the selected index, in the shape
`Probe430.agda:98-100` uses for ordinality. **If the two halves do not sit over
the same `sucV x`, the four-case account above has no first step, and that
mismatch IS the finding.**

ESTIMATE for W3: about 10 lines and under 3 seconds. BASIS: both halves are
projections of terms two delivered probes already carry. If it costs more, say
so.

Report the median wall time and the peak RSS over three forced rechecks at the
pane's caliber, for W3 alone and for the full file. The seals are opaque and
this file holds two of them: `[LJ-1.398]` met an 8 GB heap event on the
unfolding style at this class of seal (`dev/pod/audit-2026-08-20.md:128`). If
the heap wall fires, that is a result and not a failure.

## WHAT GO AND NO-GO EACH EARN

**A GO REDUCES THE WHOLE COUNTING LEG TO ONE STATEMENT ABOUT TWO ORDINALS.**
After it, every open task in this campaign that hunts an untruncated arrow
becomes optional, and `[LJ-2.5]` reads one type instead of fifty probes.

**A NO-GO IS WORTH AS MUCH.** It says the four-case account is wrong, or the
two splits do not share a carrier, or a delivered case does not accept a DATA
induction hypothesis. Each is a measured fact and each changes the next brief.

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
# `[LJ-1.440]` parked `no-match` seven times for exactly this gap
# (dev/pod/transitions/2026-08.jsonl:832). A stated NO-GO is the critic's
# input and never a close, so this routes to the critic and the critic's
# return closes the task.
id = "stop-stated"
priority = 12
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 0
  obligations_delta_min = 0
  changed_files_any = ["agents/tasks/LJ-1-447/review-of-*.md"]

[[branch]]
id = "no-go-attacked"
priority = 15
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  error_class_in = ["unsolved_meta", "universe_level", "other"]
  changed_files_any = ["agents/tasks/LJ-1-447/Probe447.agda"]
  changed_files_none = ["agents/tasks/LJ-1-447/review-of-*.md"]

[[branch]]
id = "no-go-stated"
priority = 20
action = "escalate"
head_slot = "mathematician_adversarial"

  [branch.when]
  exit_code = 42
  changed_files_any = ["agents/tasks/LJ-1-447/review-of-*.md"]

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
- CANDIDATE archive/dev/LJ-dispatch-index.md  (score 152.838)
- CANDIDATE archive/dev/JOURNAL-archived.md  (score 138.616)
- CANDIDATE archive/dev/JOURNAL.md  (score 116.480)
- CANDIDATE dev/ARCHIVE.md  (score 102.453)
- CANDIDATE archive/dev/DD-archived.md  (score 97.319)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## ARCHIVE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.

## LITERATURE (program-generated, do not edit)

Corpus search over dev/literature:
- CANDIDATE dev/literature/devlin-II5.md  (score 47.549)
- CANDIDATE dev/literature/truncation-and-selection.md  (score 41.984)
- CANDIDATE dev/literature/terms-2026-08.md  (score 28.615)
- CANDIDATE dev/literature/digest.md  (score 27.932)
- CANDIDATE dev/literature/geology.md  (score 24.944)

**ANSWER THIS BLOCK IN YOUR RETURN, under a `## LITERATURE USED` heading.** Acceptance conjunct 6 REFUSES a return without it, whatever the search found above, and `NO HIT` does not excuse the heading.

- **Name every CANDIDATE path above.** A path you never name is an unanswered duty and not a silent decline.
- **For a file you read**, cite it as `path:line` and quote the line you read. The quote must occur AT that line in that file, and the checker opens the file to confirm it.
- **For a file you did not use, DECLINE IT IN WRITING.** A decline is COMPLIANCE and never a defect: `not read`, `declined`, `not used`, `not surveyed`, or a `why not` sentence all count.
