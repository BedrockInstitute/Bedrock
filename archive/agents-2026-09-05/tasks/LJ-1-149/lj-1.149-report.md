# LJ-1.149 report: the six standing OWED markers

tier: opus (version `override`). **READING task. NO AGDA WAS RUN. No file under
`src/` was touched. No section 11 verdict cell and no `[[remaining]]` row was
edited. No commit, no push.** Every negative is marked **MEASURED** or
**INFERRED**.

One file was edited, and the brief permits it: `dev/PLAN.md:187`, the section 4
heading and prose. Section 3.1 gives the diff and the reason.

DD4: this task writes no code. The DD4 answer is in section 5.3, on the one
site where a shared-code decision is at stake.

## 0. THE REAL UNPAID DEBT, and it is not on the list the brief expected

**`dev/PLAN.md:387` states a fact that is false, and it is the fact that keeps
`[LJ-2.5]`'s evidence open.**

The line reads: `[L3.32-T261]`'s probe on the S-tower crossing was QUEUED for
an Agda slot and never ran.

**The probe RAN. MEASURED**, by reading the report and the file:

- `agents/tasks/archive/L3-32-T261/l3.32-t261-report.md:9-12`: 「The probe
  closed. `src/ProbeT261.agda` exits 0 at one cold run of 1.50 s and 124 fresh
  lines. No wall fired.」
- `agents/tasks/archive/L3-32-T261/l3.32-t261-report.md:50-54`: 「One Agda
  process at `GHCRTS=-M8g`. Exit code 0. One timed cold run: 1.50 s wall ...
  Fresh lines: 124, against the 300 stop.」
- The probe file is on disk, rehomed by `[LJ-1.141]`:
  `agents/tasks/archive/L3-32-T261/ProbeT261.agda`, 124 lines, `limit-case` at
  `:90`, the beta separation at `:56-58`.

**What ran is exactly the probe that closes `[T257]`'s weak point.**

1. `[T257]` named its own weak point at
   `agents/tasks/archive/L3-32-T257/l3.32-t257-routes.md:500-517`: it prices
   `carried-sequence` and `blockpowlim-instance` at ZERO for the GCH wing,
   worth 4,238 to 5,218, on **three negatives** (no import edge, no wing
   obligation, one circular citation).
2. `[T260]` did the read-only pass and specified the probe, but could not run
   it: `dev/ledger.toml:1272-1275`, 「both Agda slots stayed held for its whole
   dispatch」.
3. **`[T261]` ran that probe**, to `[T260]`'s own section 5 specification
   (`agents/tasks/archive/L3-32-T261/l3.32-t261-report.md:18-19`), and added
   the C-23 name sweep over every line of every wing file (`:120-124`) and the
   node-by-node citation trace (`:64-97`).
4. `[T261]` closed with the exact figure:
   `agents/tasks/archive/L3-32-T261/l3.32-t261-report.md:190-195`, 「The sum is
   4,238-5,218 naive and 5,537-7,400 calibrated, the numbers the wing does not
   pay.」

**So four live sentences understate the evidence `[LJ-2.5]` already holds.**

| site | what it says | state |
|---|---|---|
| `dev/PLAN.md:387-388` | T261's probe 「never ran」 | **FALSE.** MEASURED |
| `dev/ledger.toml:214-219` | 「[T260] supported that pricing ... and its own probe never ran」 | **TRUE of T260, STALE as a whole.** It never names T261 |
| `dev/ledger.toml:1272-1275` | 「[T260]'s probe did not run ... The probe is specified in its report section 5 for whoever has a slot」 | **STALE.** T261 had the slot and ran it |
| `dev/ledger.toml:2185-2189` | the weak point is 「Unresolved and material」 | **STALE.** T260 resolved the reading, T261 pinned it |

**WHERE THE ERROR ENTERED, and it is one commit.** `808c1c5`, 2026-08-09,
`[LJ-0.3]`'s closeout, whose own message reads 「T261's crossing probe was
queued for an Agda slot and never ran」. **The source of the error is the BRIEF
HEADER, not the report:** `agents/tasks/archive/L3-32-T261/l3.32-t261.md:3`
reads 「tier: codex (default), `--agda`. **Queued for an Agda slot.**」 That is
the state on the day the brief was WRITTEN. The closeout read the header and
never opened the report.

**This is C-41's family exactly.** Each of those four sentences still reads
true in isolation, and the world it described changed on 2026-08-09. Nothing
mechanical can see it, because a brief header is not a claim a checker parses.

**WHAT IS STILL GENUINELY OWED, and it is a different probe.** DD2
(`dev/PLAN.md:169`) asks for 「the queued `[L3.32-T261]`-**class** probe」 plus
「one bounded op-clause times sixteen」. That is the J-side clause pricing that
`[L3.32-T263]` left open:
`agents/tasks/archive/L3-32-T263/l3.32-t263-fof.md:3-4`, 「At the delivered
formulas, **none of the sixteen** operation graphs is Δ₀」, and `:171-178`,
sixteen fresh bounded clauses are owed and the bounding terms are 「new and
unmeasured」. **That debt is LIVE.** It is not T261's probe, and the plan text
conflates the two.

## 1. THE SIX, ONE ROW EACH

| # | site | what is owed, to whom | verdict |
|---|---|---|---|
| 1 | `dev/PLAN.md:187` | a re-derived target skeleton, to DD2 | **LIVE, owned, and the prose carried two false clauses** |
| 2 | `dev/PLAN.md:386` | two pieces of evidence, to `[LJ-2.5]` | **ONE PAID AND MISREPORTED, ONE LIVE** |
| 3 | `dev/PLAN.md:513` | a placement gate, to DD24 | **PAID by the next row, and the reassurance it returned is what failed** |
| 4 | `dev/PLAN.md:548` | the twelve-row bridge, to `Condensation` | **LIVE, priced at 38 lines, and NOBODY OWNS IT** |
| 5 | `dev/PLAN.md:561` | `AllCodes` in `K`, to the code set | **PAID, and the cell mis-states its own report** |
| 6 | `dev/ledger.toml:732` | an owner's ruling between two routes | **DEAD, and the ledger already says so in machine-readable form** |

## 2. THE VERDICTS, WITH EVIDENCE

### 2.1 `dev/PLAN.md:187`, the target skeleton: LIVE, and it has an owner

**What is owed, to whom, and what discharges it.** A target skeleton for the
two-tower route is owed to DD2, and `[LJ-2.3]` discharges it.

**LIVE.** `dev/PLAN.md:635`, the `[LJ-2.3]` row, verdict `planned`, whose text
reads 「Delivers section 4's skeleton」. So the debt is registered, it is not
residue, and the heading was simply missing its owner's name.

**TWO CLAUSES IN THE PROSE WERE FALSE. Both MEASURED.**

1. **The part level names a part that does not exist.** The prose said the part
   level 「(Base, FOL, ZF, V, L, Landmarks)」 is fixed. **`src/` has no `ZF/`.**
   MEASURED by `ls src/`: `Base`, `FOL`, `L`, `V`, `Everything.lagda.md`,
   `Landmarks.lagda.md`, `README.md`. MEASURED again by
   `find src archive/src -maxdepth 1 -iname "ZF*"`, which returns nothing. The
   reason is on the record: `src/README.md:53`, 「Re-cut from `ZF/` (PLAN §4
   ledger)」. This predates the route change; it is C-32's shape, a threshold
   outliving its tree.
2. **The provisional layout waits on a row that will never run.** The prose
   said the below-part layout is provisional 「until the `[L3.10]`
   re-layering」. `[L3.10]` is a child of `[L3]`, and `dev/PLAN.md:346` reads
   「SUPERSEDED WHOLESALE 2026-08-09 by the `LJ` series」. Its own row is at
   `archive/dev/STATUS-archived.md:84`, status PLANNED. **Per C-41 the code is
   NOT renumbered**; the fix is to give it its home and say the condition is
   dead.

**A THIRD DEFECT IS OUT OF MY WRITE SCOPE, and I name it rather than fix it.**
`dev/PLAN.md:189` names `src/README.md` as an authority. That file's own
section 「Reserved namespaces (currently empty, marked with `.gitkeep`)」
(`src/README.md:94-103`) lists `V/` and `L/` as reserved and empty. **Both are
non-empty today.** MEASURED by `ls src/V src/L`. The named authority carries a
stale section, and no checker reads it.

### 2.2 `dev/PLAN.md:386`, the two pieces of evidence: ONE PAID, ONE LIVE

**What is owed, to whom, and what discharges it.** Two measurements are owed to
`[LJ-2.5]`, the architecture ruling. Section 0 gives the whole trace.

- **T261's probe: PAID, 2026-08-09, and reported as unpaid ever since.**
  MEASURED. Evidence in section 0.
- **T257's weak point: PAID AS A READING, and its strength is stronger than
  four live documents say.** `[T260]` gave the import-graph pass `[T257]` asked
  for at `l3.32-t257-routes.md:511-517`; `[T261]` then pinned it with the probe
  and the C-23 sweep. What is NOT paid is a second independent line pass: the
  band still rests on one agent's comparison
  (`dev/ledger.toml:212`, `lines_source = "[L3.32-T257], one pass, one
  agent"`).
- **The sixteen bounded op-clauses: LIVE and unmeasured.** MEASURED that no
  probe covers them: `agents/tasks/archive/L3-32-T263/l3.32-t263-fof.md:3-4`
  and `:171-178`. `dev/ledger.toml:2259` carries the same,
  `t259_crossing = "VIABLE but UNPRICED ... sixteen fresh Delta-0 clauses are
  owed"`.

**A SECOND DEFECT AT THIS SITE: THE DEBT HAS TWO OWNERS AND THE PROSE NAMES
THE WRONG ONE.** `dev/PLAN.md:390` says `[LJ-2.3]` surveys the two pieces.
`dev/PLAN.md:633`, the `[LJ-2.0]` row, says `[LJ-2.0]` re-prices them and
「Gates LJ-2.5」. **`[LJ-2.0]` was registered ONE COMMIT AFTER the prose was
written**, both on 2026-08-09: `c5f994b` wrote `dev/PLAN.md:386-390`, and
`808c1c5` added the `[LJ-2.0]` row without updating it. MEASURED by
`git log -S` on both strings and `git merge-base --is-ancestor`. Also
`dev/PLAN.md:637`, the `[LJ-2.5]` row, lists its dependencies as 「LJ-2.0, 2.1,
2.2 and 2.4」 and does not list `[LJ-2.3]` directly.

### 2.3 `dev/PLAN.md:513`, `[LJ-1.57-A]`'s gate: ALREADY PAID

**What is owed, to whom, and what discharges it.** A placement gate is owed to
DD24, and the next dispatch ran it.

**PAID. MEASURED.** `[LJ-1.58]` IS that gate. Its brief carries `[LJ-1.57-A]`'s
own numbers as its premise: `agents/tasks/archive/LJ-1-58/LJ-1.58.md:22`, 「after
placing it as-is | 5,524 | 121.5 | **0.02200**」, and `:25`, 「Placing it as
spelled puts the file 1.73x over the bar.」 The gate returned AMBER at 0.01765
marginal, whole file 0.01202
(`agents/tasks/archive/LJ-1-58/lj-1.58-report.md:10-16`).

**THE INTERESTING PART IS WHICH HALF SURVIVED.** `[LJ-1.57-A]` predicted
**0.0220, 1.73x**. `[LJ-1.58]` answered with a reassurance:
`agents/tasks/archive/LJ-1-58/lj-1.58-report.md:233-234`, 「a whole 884-line
placement at the measured rate would land the file at about **0.0125**, also
under the bar」.

Today `L/Condensation` measures **0.0187 at 6,445 lines and 120.61 s**
(`agents/tasks/LJ-1-145/LJ-1.145.md:18`), and the wing aggregate is 0.0187,
1.58x (`agents/tasks/LJ-1-147/runs/before-1.txt:18`).

- `[LJ-1.57-A]`'s 0.0220 is **18 percent high**.
- `[LJ-1.58]`'s 0.0125 is **33 percent low**.

**So the OWED marker was the better prediction, and the gate that discharged it
returned the number that failed.** The debt is paid; the row should be left as
the dated record it is, and the lesson belongs where `[LJ-1.145]` and
`[LJ-1.147]` are already working.

### 2.4 `dev/PLAN.md:548`, `[LJ-1.76-A]`'s bridge: LIVE, PRICED, AND UNOWNED

**What is owed, to whom, and what discharges it.** `src/L/Condensation.lagda.md`
takes `twelve-out` and `twelve-back` as hypotheses; something must supply them.
Placing about 38 in-fence lines in
`src/L/Condensation/TwelveAgree.lagda.md` discharges it.

**LIVE. MEASURED, by grep over `src/`.** The bridge is NOT in the tree:

- `src/L/Condensation.lagda.md:6692` and `:6695` still declare `twelve-out` and
  `twelve-back` as module PARAMETERS of `SatGraphAgree`; `:6935` and `:6938`
  repeat them for `LeafAgree`.
- `src/L/Condensation/TwelveAgree.lagda.md:294` and `:315` export `out` and
  `back` at the module-local `twelveB`, which is a different `Formula` term.
- Grep for `twelve-out` over `src/` returns hits in `Condensation.lagda.md`
  only. Nothing supplies them.

**THE FINDING IS NOT THE DEBT. IT IS THAT NOBODY OWNS IT.**
`agents/tasks/LJ-1-144/lj-1.144-report.md:9-22` proved the bridge buildable in
a probe at the consumer's exact types, exit 0, and priced it at **about 38
in-fence lines and about 3.5 s, with no new master**. **No PLAN section 11 row
is registered to place it.** MEASURED by reading every row from
`dev/PLAN.md:624` to `:629`: `[LJ-1.145]` diagnoses seconds, `[LJ-1.146]`
prices `levelIn` and `cover`, `[LJ-1.147]` seals `satGraphAt`, `[LJ-1.148]`
tests DD24's tolerance, `[LJ-1.149]` is this audit. **None places the bridge.**

**So the marker is correct and the plan is short one row.** This is C-34's
shape from the other side: a return named a cure and priced it, and the price
then sat with no dispatch behind it.

### 2.5 `dev/PLAN.md:561`, `[LJ-1.83-A]`'s code set: PAID, and the cell misquotes its own report

**What is owed, to whom, and what discharges it.** A membership fact is owed to
the code-set slot `C`, and `[LJ-1.90]` supplied it.

**THE CELL AND ITS REPORT DO NOT AGREE, and the difference is one symbol.**

- The cell (`dev/PLAN.md:561`) says the real `C` is `AllCodes`, 「needing
  AllCodes **in** K, unproved」.
- Its report says the opposite relation:
  `agents/tasks/archive/LJ-1-83/lj-1.83-report.md:47-49`, 「its decomposition
  facts would need `AllCodes ⊆ K`, a code-depth content fact」.

**PAID AS THE CELL WRITES IT. MEASURED.** `K = LsetS lam ordλ`
(`agents/tasks/archive/LJ-1-83/lj-1.83-report.md:24-26`), so `AllCodes ∈ K` is
`AllCodes A ∈ Lset lam`. `[LJ-1.90]` supplied exactly that:
`agents/tasks/LJ-1-90/lj-1.90-report.md:84-99`, three machine-checked steps,
the term `AllCodes∈Lλ` at `agents/tasks/LJ-1-90/ProbeLJ190A.agda:193-194`,
instantiated at `:199`. `agents/tasks/LJ-1-90/lj-1.90-report.md:112-117` says
it in C-38's words: 「`AllCodes A ∈ Lset lam` is now supplied, not restated, by
a VALUE at a real site.」

**PAID AS THE REPORT WRITES IT, ONE STEP AWAY. INFERRED.** `K` is transitive at
the frame (`agents/tasks/archive/LJ-1-83/lj-1.83-report.md:52-56`,
`module CodeFacts (T : V) (transT : ...)`), so `AllCodes A ∈ K` gives
`AllCodes A ⊆ K`. **I did not run Agda and no probe states that step**, so this
half is INFERRED, not MEASURED.

**ONE CONDITION THE CELL DOES NOT CARRY, and it is load-bearing.**
`agents/tasks/LJ-1-90/lj-1.90-report.md:101-107`: 「`lam` is not arbitrary. It
must be chosen with room above the code set's stage. The frame's own data ...
does not imply `AllCodes A ∈ Lset lam` at an arbitrary `lam`.」

**AND THE SUBSTITUTION MAY NEVER BE NEEDED.**
`agents/tasks/archive/LJ-1-83/lj-1.83-report.md:41-44`: 「No consumer requires
`C` to be a particular code set such as the delivered `AllCodes`.」 That is
D-30: price what the consumer needs, never the general law. So `C = K` is a
probe convenience that no consumer has yet asked to replace.

### 2.6 `dev/ledger.toml:732`, `blockpowlim-instance`: DEAD, and the file says so

**What is owed, to whom, and what discharges it.** The owner's ruling between
REVIVAL and RE-FORMULATION is owed, and only the two-tower route's own
accounting can make the question live again.

**THE BRIEF'S READING IS WRONG, and I say so plainly.** The brief calls it 「a
LIVE cost row」 because `naive_low = 1619` and `trophy = "BOTH"`. **The ledger
declares every `[[remaining]]` row stale, in machine-readable form.**

- `dev/ledger.toml:136-137`: `remaining_stale = true`, with
  `remaining_stale_rearm = "LJ-2.2: rebuild the [[remaining]] rows for the
  two-tower route, then set this false"`.
- `dev/ledger.toml:119-123`: 「Every one of them prices rud-route work ... so an
  endpoint built from them adds rud-route work to an internalization base,
  which is not a projection of anything real.」
- **The flag is READ.** MEASURED by grep over `scripts/`:
  `scripts/ledger.py:807` and `:966` both branch on `remaining_stale`, and
  `:969` prints the refusal with its re-arm. So `--brief` refuses the endpoint
  rather than quoting the row.

**So the marker is DEAD for the current route, and its own file already carries
the correction.** The defect is not the row. The defect is that the row's own
1,000-word `gate` field re-argues the fork with no pointer back to the flag
that suspended it, so a reader who lands on `:738` cannot see it.

**A SECOND, SHARPER INCONSISTENCY INSIDE ONE FILE.** `dev/ledger.toml:734`
carries `trophy = "BOTH"`. `dev/ledger.toml:1264-1266` carries the measured
opposite: 「SO THE WING DOES NOT PAY `carried-sequence` OR
`blockpowlim-instance`, 4,238-5,218 naive」. One file says the GCH trophy pays
this row and also that it does not. **`trophy_split_suspended = true`
(`dev/ledger.toml:116`) is why nothing fires.**

## 3. WHAT I CHANGED, AND WHAT I PROPOSE

### 3.1 APPLIED: `dev/PLAN.md:187`, the only site the brief opens to me

Heading, and the two false clauses replaced by the measured facts. The diff is
6 insertions and 2 deletions in one section.
`.venv/bin/python scripts/lint-prose.py --check` is silent and
`.venv/bin/python scripts/check-rule-ids.py` reports 「clean (45 files, 142
lessons, 66 decisions)」.

What the new text does:

1. Names `[LJ-2.3]` in the heading, so the debt is owned.
2. States the measured part level, Base, FOL, V, L and Landmarks, and cites
   `src/README.md:53` for where `ZF/` went.
3. Gives `[L3.10]` its archive home per C-41, says its condition is dead, and
   hands the arrangement question to `[LJ-2.3]`.

### 3.2 PROPOSED, for the orchestrator to apply

**(a) `dev/PLAN.md:386-390`, the paragraph. It is not a verdict cell, but it is
outside my write scope, so I propose it.**

> **TWO PIECES OF EVIDENCE THE RULING IS OWED, and the record on one of them
> was wrong until `[LJ-1.149]` read it.** `[L3.32-T261]`'s probe on the
> S-tower crossing **RAN**, on 2026-08-09: exit 0, one cold run of 1.50 s over
> 124 fresh lines, at `agents/tasks/archive/L3-32-T261/ProbeT261.agda`, and it
> is the probe `[T260]` specified and could not run. It measured that the GCH
> wing pays neither `carried-sequence` nor `blockpowlim-instance`, the
> 4,238 to 5,218 that `[L3.32-T257]` declared as its own weak point. **This
> paragraph and three `dev/ledger.toml` notes said it never ran, from
> 2026-08-09 to 2026-08-13**, because `[LJ-0.3]`'s closeout read the brief
> header rather than the report. **WHAT IS STILL OWED IS DIFFERENT AND
> SMALLER:** one bounded op-clause priced and multiplied by sixteen, which
> `[L3.32-T263]` left unmeasured, and a second independent pass on `[T257]`'s
> line comparison, which is still one agent and one pass. **`[LJ-2.0]` owns
> both** and gates `[LJ-2.5]`; `[LJ-2.3]` reads them into the reuse map.

**(b) `dev/ledger.toml:214-219`, `lines_weak_point`.** Replace the second
sentence.

> `[T260]` supported that pricing on import-graph facts and its own probe never
> ran. **`[T261]` THEN RAN IT, 2026-08-09**, exit 0 at 1.50 s over 124 lines
> (`agents/tasks/archive/L3-32-T261/l3.32-t261-report.md:9-12`), and added the
> C-23 name sweep. **The wing-pays-zero half is pinned at measured strength.**
> What stays weak is the line comparison itself: one pass, one agent.

**(c) `dev/ledger.toml:1272-1275`.** Replace 「STRENGTH: import-graph FACTS plus
obligation READINGS ... The probe is specified in its report section 5 for
whoever has a slot」 with:

> STRENGTH: import-graph FACTS, obligation READINGS, **and the probe, which
> `[T261]` ran on 2026-08-09 to this report's own section 5 specification**
> (`agents/tasks/archive/L3-32-T261/l3.32-t261-report.md:18-19`, `:50-54`).
> This IS pinned at measured strength.

**(d) `dev/ledger.toml:2185-2189`.** The last words are 「Unresolved and
material」. Replace with 「Resolved 2026-08-09 by `[T260]`'s pass and `[T261]`'s
probe; see the `lines_weak_point` field. The line comparison itself is still
one pass by one agent.」

**(e) `dev/ledger.toml:738`, the `blockpowlim-instance` gate field.** Do not
rewrite the fork narrative. **Prefix one sentence** so a reader who lands here
sees the flag:

> **THIS ROW IS SUSPENDED. `remaining_stale = true` (`:136`) covers it, and
> `ledger.py --brief` refuses the endpoint that would quote it. The fork below
> is the RETIRED rud route's, and `[LJ-2.2]` decides whether the two-tower
> route has an heir to it. `trophy = "BOTH"` above is inconsistent with
> `:1264-1266`, which measured that the GCH wing pays this row zero;
> `trophy_split_suspended` (`:116`) is why no checker fires.**

**(f) `dev/PLAN.md:561`, the `[LJ-1.83-A]` verdict cell. I recommend NOT
striking it, and correcting one symbol instead.** The cell is a dated record of
what that audit found. But it misquotes its own report: `⊆`, not `∈`. Proposed
cell text, within the 200-character cap at 174 characters:

> `The real C is AllCodes, needing AllCodes ⊆ K, unproved. PAID by LJ-1.90 at a stage naming lam. The stop at witK is independent of the choice`

**(g) `dev/PLAN.md:513` and `:548`. Change NOTHING.** Both rows are correct
records of their day, and both debts resolved after them, one paid and one
still open. `[LJ-1.58]` already carries the discharge of `:513`, and
`[LJ-1.144]` already carries the settlement of `:548`. Striking a dated verdict
would delete the evidence that `[LJ-1.57-A]` predicted better than its own gate
did.

**(h) REGISTER A ROW FOR THE BRIDGE.** This is the one action item that is a
build. Section 4.

## 4. WHAT NEEDS A DISPATCH, AND WHAT IT COSTS

| # | work | price, and its basis | who |
|---|---|---|---|
| 1 | **Place the twelve-row bridge** in `src/L/Condensation/TwelveAgree.lagda.md` | **about 38 in-fence lines, about 3.5 s, no new master.** MEASURED by `[LJ-1.144]`'s probe (`agents/tasks/LJ-1-144/lj-1.144-report.md:16-21`) | unregistered. Needs a row |
| 2 | **Price one bounded op-clause and multiply by sixteen** | UNMEASURED. `[L3.32-T263]` left the bounding terms 「new and unmeasured」 (`l3.32-t263-fof.md:171-178`) | `[LJ-2.0]`, registered |
| 3 | **A second independent pass on `[T257]`'s line comparison** | UNMEASURED. `dev/ledger.toml:212` records one pass, one agent | `[LJ-2.0]`, registered |
| 4 | **Apply 3.2 (a) to (f)** | text only | the orchestrator |

**Item 1 is the cheapest unbought result in this audit.** It converts C-35's
「no consumer」 into the consumer's exported type for a measured 38 lines. It
does NOT discharge anything: `agents/tasks/LJ-1-144/lj-1.144-report.md:46-56`
says so, and names the widest unmeasured term as the frame instantiation, 29
consumer-side facts classed PROVABLE 1 and NEW CONTENT 28.

## 5. WHAT `[LJ-2.5]` STILL NEEDS

### 5.1 What it already has, and did not know it had

**The 4,238 to 5,218 question is settled at measured strength.** `[T261]`'s
probe closed the one obligation `[T260]` could not rule out by reading, and the
C-23 sweep found that **no file in the wing's 87-module closure names both
towers** (`agents/tasks/archive/L3-32-T261/l3.32-t261-report.md:118-122`), so
the wing cannot even STATE a cross-tower obligation. That is a structural fact,
and it is stronger than any count.

**One caution `[T261]` recorded and `[LJ-2.5]` must carry**
(`l3.32-t261-report.md:181-185`): after the choice re-home lands, the GCH
closure will mechanically reach the bridge through Hull's re-pointed order.
**That closure SHADOW is not a refutation of the settlement.**

### 5.2 What it still needs

1. **The sixteen bounded op-clauses, priced.** `[LJ-2.0]`. This is the only
   term DD2 names as blocking, and DD2 says the asymmetry is 「a direction with
   an unpriced magnitude」 until it lands.
2. **A second pass on the line benchmark.** `dev/ledger.toml:213`,
   `lines_state = "NOT YET CLEAR ENOUGH TO BIND"`, unchanged.
3. **The two suspended flags cleared:** `remaining_stale` and
   `trophy_split_suspended`, both re-armed on `[LJ-2.2]` and `[LJ-2.1]`.

**Nothing that is queued for an Agda slot is blocking `[LJ-2.5]` today.**
MEASURED, by the search that produced this report: I grepped `\bowed\b`
case-insensitively over `dev/`, `dev/memos/` and `src/`, read every hit in
`dev/PLAN.md` and `dev/ledger.toml`, and traced the two evidence items to their
archived reports and probe files.

### 5.3 The DD4 answer

**One site in this audit carries a shared-code decision, and it is item 1.**
`[LJ-1.144]` already answered it generically:
`agents/tasks/LJ-1-144/lj-1.144-report.md:26-33` refuses retirement because the
delivered shape, two six-row partials and one composer, **was measured rather
than chosen** (`[LJ-1.73]`, `[LJ-1.74]`, `[LJ-1.74-A]`). That shape is what a
second tower re-instantiates. A retirement would buy 842 lines back and then
buy them again at the same price, which is the DD4 loss written as arithmetic.
**Nothing in this audit proposes writing anything fixed.**

## 6. NEGATIVES, EACH CLASSIFIED

| negative | class | the search |
|---|---|---|
| `src/` has no `ZF/` part | **MEASURED** | `ls src/`; `find src archive/src -maxdepth 1 -iname "ZF*"`, empty |
| Nothing in `src/` supplies `twelve-out` or `twelve-back` | **MEASURED** | `grep -rn "twelve-out\|twelve-back" src/`, hits in `Condensation.lagda.md` only |
| No PLAN row is registered to place the bridge | **MEASURED** | read `dev/PLAN.md:624-629`, every row from `[LJ-1.144]` to `[LJ-1.149]` |
| The sixteen op-clauses are unpriced | **MEASURED** | `agents/tasks/archive/L3-32-T263/l3.32-t263-fof.md:3-4`, `:171-178`; `dev/ledger.toml:2259` |
| `[L3.10]` has no live row | **MEASURED** | `grep -rn "L3\.10" dev/` returns `PLAN.md:189` and three memos; `dev/PLAN.md:346` supersedes `[L3]` wholesale |
| `remaining_stale` is read by a tool | **MEASURED** | `grep -n "remaining_stale" scripts/*.py`, four hits in `scripts/ledger.py` |
| `AllCodes A ⊆ K` follows from the supplied membership | **INFERRED** | transitivity of `K` at `lj-1.83-report.md:52-56`. **No probe states this step and I ran no Agda** |
| Retiring the `*Agree` cluster would strand the 2,636-line row block | **INFERRED**, and it is `[LJ-1.144]`'s own classification | `agents/tasks/LJ-1-144/lj-1.144-report.md:41-45` says it measured the block and did not audit every module inside it |

## ARCHIVE USED (DD18)

- `agents/tasks/archive/L3-32-T261/l3.32-t261-report.md:9-12`, `:18-19`,
  `:50-54`, `:64-97`, `:118-124`, `:181-195`. The probe ran; the citation
  circle; the import graph; the 4,238 to 5,218 sum.
- `agents/tasks/archive/L3-32-T261/l3.32-t261.md:3`. The brief header that says
  「Queued for an Agda slot」, which is the source of the false claim.
- `agents/tasks/archive/L3-32-T261/ProbeT261.agda`, 124 lines, `limit-case` at
  `:90`, separation at `:56-58`.
- `agents/tasks/archive/L3-32-T257/l3.32-t257-routes.md:498-530`. The declared
  weak point and the measurement that closes it.
- `agents/tasks/archive/L3-32-T263/l3.32-t263-fof.md:3-4`, `:164-178`. None of
  the sixteen is Δ₀; the clauses are new and unmeasured.
- `agents/tasks/archive/LJ-1-57/lj-1.57-report.md` and
  `agents/tasks/archive/LJ-1-58/LJ-1.58.md:22-25`,
  `agents/tasks/archive/LJ-1-58/lj-1.58-report.md:10-16`, `:228-240`. The gate
  and its reassurance.
- `agents/tasks/archive/LJ-1-83/lj-1.83-report.md:8-15`, `:24-56`. `C = K`,
  `K = LsetS lam ordλ`, the `⊆` form of the debt, `CodeFacts` transitivity.
- `agents/tasks/LJ-1-90/lj-1.90-report.md:1-40`, `:84-120`;
  `agents/tasks/LJ-1-90/ProbeLJ190A.agda:193-194`, `:199`. The membership,
  supplied.
- `agents/tasks/LJ-1-144/lj-1.144-report.md:9-33`, `:41-56`, `:58-90`. The
  bridge, its price, its consumers, its C-38 limit.
- `agents/tasks/LJ-1-145/LJ-1.145.md:18`, `:52`;
  `agents/tasks/LJ-1-147/runs/before-1.txt:18`. Today's ratio.
- `archive/dev/STATUS-archived.md:61`, `:84`. `[L3.10]`'s home, per C-41.
- `archive/dev/DECISIONS-archived.md:32`. Archived D5's own text, which fixes
  the part level and names `src/README.md` as the live authority.
- `dev/memos/target-skeleton-d5.md:1-14`. The superseded skeleton, which repeats
  the `ZF` part level.
- `dev/PLAN.md:169` (DD2), `:171` (DD5), `:346`, `:386-390`, `:513`, `:548`,
  `:561`, `:624-637`. Read whole for DD2 and DD5, as the brief required.
- `dev/ledger.toml:105-145`, `:205-220`, `:729-740`, `:1255-1285`,
  `:2180-2200`, `:2259`. The four suspension flags and every note on the weak
  point.
- `dev/LESSONS.md:3657` (C-41), and the recon bundle from
  `scripts/rules.py --for recon`.
- Commits `c5f994b` and `808c1c5`, both 2026-08-09, for where the false claim
  entered.

## LITERATURE (DD18)

Nothing in the literature governs a plan marker.

## MANDATORY RULES, AND WHERE EACH LANDED

`.venv/bin/python scripts/rules.py --for recon` returned D-10, C-22, P-l and
D-26, and all four were read.

- **C-41** is the whole task. Four sentences read true after their world
  changed. `[L3.10]` keeps its number and gains its home.
- **C-32**, a threshold outliving its tree: the `ZF` part level, fixed by a
  ruling and re-cut out of `src/` before the route ever changed.
- **C-35**: section 2.4. The bridge is the C-35 cure and nobody bought it.
- **D-10**: I checked the truth of each recorded target before pricing it, and
  two were false as recorded (`dev/PLAN.md:387`, `dev/PLAN.md:561`).
- **D-30**: section 2.5. No consumer asks for `C = AllCodes`.
- **C-34**: section 2.4. `[LJ-1.144]` priced its cure and the price has no
  dispatch behind it.
- **C-22**: this file was created as a skeleton before the first site was read.
- **C-39**: the brief forbade Agda, section 11 edits and `[[remaining]]` edits.
  I obeyed all three and report the door behind each wall in section 3.2.
- **C-40**: the consumers of `dev/PLAN.md:187` are `dev/memos/target-skeleton-d5.md`
  and `dev/memos/process-tensions.md:18`, and both repeat the `ZF` part level.
  I did not edit them; they are out of my write scope and I name them here.
