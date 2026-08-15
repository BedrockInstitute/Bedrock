# LJ-1.311: DD25 review of `[LJ-1.309]`'s no-hit sweep

**STATUS: COMPLETE.** Skeleton written in the first five minutes (C-22),
filled incrementally. Every negative is marked MEASURED or INFERRED, in those
words. ASD-STE100 applies. Machine load reported beside every absolute figure.

## VERDICT

**SPLIT.** The NO-GO outcome and the DO-NOT-FUND recommendation STAND, and
the census's three sites are real; but three of the report's load-bearing
measurement claims are FALSE, and one of them rests on reading a report's
excerpted table where the raw file carried the row.

- **UPHELD, by re-derivation and re-measurement:** no site at depth 3 or
  more exists in `src/`; the deepest full-chain site is depth 2; the three
  census sites are exactly as reported; the 400-second depth-4 prize is not
  in the tree, in EITHER iterate channel; Key.lagda.md is in neither DD4
  closure; the cure is not worth funding.
- **OVERTURNED:** "Only `sucIter` builds a numeral stage iterate in `src/`"
  (attack 1); "`splitKey∈` does not appear in `[LJ-1.292]`'s profile...
  0 ms to 522 ms" (attack 2); "the half-cure... 42 times worse" (attack 5).

## THE PREMISES, VERIFIED OR REFUTED (C-44, both directions)

| the brief's premise | verdict |
|---|---|
| the census is three sites at `Key.lagda.md:118-120`, `:129-131`, `:133`, all depth 2 | **VERIFIED by reading.** Rank 1: `pair∈`'s type `T (sucIter 2 σ)` against `T-pr`'s output `T (sucV (sucV σ))`. Rank 2: the outer `T-pr`'s output `T (sucV (sucV (sucIter 5 σ)))` against the conclusion `T (sucIter 7 σ)`. Rank 3: the inner `T-pr`'s output `T (sucV (sucV (sucIter 3 σ)))` against the outer slot `T (sucIter 5 σ)` |
| the ladder is 219 / 9,286 / 419,218 ms at depths 2 / 3 / 4, `lj-1.292-report.md:37-39` | **VERIFIED as the reading.** The report's bisect table prices `w2` 219, `w3` 9,286, `w4` 419,218. My re-anchors: `b2` 215, `b3` see attack 3 |
| DD24's gap is 60.0 s, `dev/ledger.toml:303-304` | **VERIFIED.** "At 11,926 lines the on-bar allowance is 125.4 s, the wing measures 185.41 s, and the gap is 60.0 s" |
| `[LJ-1.309]` refuted `[LJ-1.292]`'s "`pair∈` has no `sucIter` mismatch" | **VERIFIED, and now measured both ways.** My E1/E2 controlled pair moves the charge with the spelling: `pair∈` 237 ms respelled to nothing, `paramEnv∈` 0 to 242 ms. The refutation stands |
| the brief's own "Condensation is about 132 s, about 62 percent of the wing" | **PARTLY WRONG, and I correct my own brief.** 132.28 s is right ([LJ-1.218]); 132.28/185.41 is 71.4 percent, not 62 |

## ATTACK 1: is `sucIter` the only iterate spelling?

**NO. MEASURED. A second numeral iterate exists and the sweep's filter cannot
see it: `#_`, the library's numeral, defined by
`# zero = ∅; # suc n = sucV (# n)` at
`Cubical/HITs/CumulativeHierarchy/Constructions.agda:164-166`.**

Textual findings (all measurements in the sections below):

- Condensation counts VERIFIED: 12 lines carry `sucV` (one is the `open` at
  `:66`), ZERO `sucIter`. MEASURED by grep.
- The written-chain census VERIFIED: exactly SEVEN `sucV (sucV` occurrences in
  FIVE files, single-line and multiline (perl `-0777`) agree; deepest explicit
  chain is depth 3 at `EnvSupply.lagda.md:216`, matched spelling. MEASURED.
- OTHER iterates examined: `numeral` (ZFModel:352) is a record field, opaque,
  cannot unfold. `numeralV` (V/Model:185) iterates `∪`/pairing, not `sucV`;
  `numeralV≡#` is propositional (Numerals-era lemma), so a definitional
  conversion would ERROR, not cost. `numeralL` (Numerals:175) iterates `sucʟ`;
  no `sucʟ (sucʟ` chain exists anywhere. MEASURED by grep. `finiteStage
  n = Lset (# n)` (Finite:823) is `Lset` composed with `#`; all its uses are
  matched-spelled. MEASURED by reading the grep.
- **A depth-2 `#`-flavored mixed-spelling CANDIDATE the census missed:
  `src/L/Choice/Name.lagda.md:129-135`, `pr∈limit.both`.**
  `Lset-mono (#∈ω (suc (suc (k + j)))) (pr∈Lset-suc (# (k + j)) x y ...)`
  forces the conversion `Lset (sucV (sucV (# (k + j))))` ≡
  `Lset (# (suc (suc (k + j))))`, a depth-2 explicit chain against a numeral
  iterate. Derived by reading; its delivered price is MEASURED at 17 ms
  (NameCtrl run, below).
- The Name site is the ONLY `#`-flavored depth-2 instance: the sole depth-2
  chain EMITTER in the tree is `pr∈Lset-suc` (Basic:596-599) and its generic
  twin `T-pr`; every use of `pr∈Lset-suc` is Name:131 (numeral `#` base),
  Bound:134 and Key:150 (parameter instantiation, type-matched). MEASURED by
  grep over uses.

### THE MEASUREMENT (Bridge probe, `Bridge.lagda.md`, run `runs/bridge3.out`)

One agda process, `GHCRTS="-A64m -I0 -M8g"`, wall 13.17 s, exit 0, ZERO
sibling agda binaries at start (C-12 slot count 0), load average about 9
(busy machine; all figures from the same run, so the comparisons hold).

| arm | the conversion | ms |
|---|---|---:|
| `b2` | sucIter anchor, depth 2, variable base | **215** |
| `x2` | sucIter iterate at a `#` base, depth 2 | **212** |
| `h1` | `#` depth 1 | not charged |
| `h2` | `#` depth 2, bare | **not charged** |
| `hL2` | **the Name site's own setting**, `Lset` level, depth 2 | **not charged** |
| `hsub2` | `#` depth 2, subject flavor under `ω` | not charged |
| `hm2` | matched control | not charged |
| `h3` | `#` depth 3 | **249** |
| `h4` | `#` depth 4 | **10,903** |

"Not charged" means below the profiler's reporting threshold (the same
instrument charges `b2` 215 ms in the same run, so this is not instrument
blindness).

**FOUR FINDINGS, ALL MEASURED.**

1. **A second numeral iterate EXISTS** (`#_`), and the `sucIter` filter is
   formally incomplete: `[LJ-1.309]`'s sentence "Only `sucIter` builds a
   numeral stage iterate in `src/`. MEASURED" is FALSE.
2. **The one `#`-flavored depth-2 candidate, Name:129-135, is PAID 17 ms
   delivered** (the `both` block's whole charge), and its isolated
   conversion elaborates below the threshold (`hL2`). Seventeen milliseconds
   is not a prize in any arithmetic.
3. **The iterate function decides the cost, not the base** (`x2` 212 against
   `b2` 215), so a consumer instantiating Key's generic `σ` at a numeral
   would still pay the sucIter price. No delivered consumer does: EnvSupply's
   `envSetK` passes a module-parameter `σ` (EnvSupply.lagda.md:144-145),
   MEASURED by grep.
4. **The `#` ladder is the sucIter ladder shifted down two rungs**: depth 3
   costs 249 ms (against sucIter's 219 at depth 2) and depth 4 costs 10,903 ms
   (against 9,286 at depth 3); the depth-3-to-4 step multiplies by 44, the
   same super-linear shape R-40 records. **A `#`-flavored depth-4 site would
   be worth about 11 s, not 400 s, and none exists**: no explicit chain of
   depth 3 or more sits over any base outside EnvSupply's matched `δ₃`.
   MEASURED.

### What that makes of Condensation

- Condensation's module total is 132.28 s ([LJ-1.218], 2026-08-14, re-measured
  after the chapter's rebuild; the 08-09 cold profile's 9.4 s predates the
  rebuild). The brief's "62 percent of the wing" is wrong arithmetic:
  132.28/185.41 = 71.4 percent. MEASURED.
- Condensation's cost has a recorded attribution: [LJ-1.283]'s triage ranks
  `SatGraphB.satGraphB` (`:2294`), `SatGraphB.twelveB` (`:2236`) and
  `closedBS` (`:1586`) as its cost carriers; all three sites match today's
  bytes. R-41 is NOT Condensation's mechanism. MEASURED (0 `sucIter`, no
  chain-vs-iterate site).

## ATTACK 2: the unresolved 522 ms

**SETTLED, and it reconciles to about 25 ms, not to 0 and not to 522.
`[LJ-1.309]`'s premise was FALSE: the raw profile always carried the row.**

- `agents/tasks/LJ-1-292/runs/k1.out:26` charges
  `LJ-1-292.ControlKey.KeyOver.splitKey∈ 26ms`. **MEASURED, in the file
  `[LJ-1.309]` cited.** [LJ-1.292]'s REPORT table (its section 2) was a
  SELECTED EXCERPT of k1.out's 42 rows: it kept rows at 12 to 14 ms and
  dropped `splitKey∈`'s 26 ms row, among others. `[LJ-1.309]` then measured
  "absence in a table reporting down to 12 ms" against the EXCERPT, not the
  raw file, and built an INFERRED Miscellaneous-attribution hypothesis on a
  false absence.
- **My own verbatim copy reproduces it: `KeyOver.splitKey∈` 24 ms**
  (`runs/key-e1.out`, wall 4.998 s, exit 0, total 3,761 ms against k1's
  3,974 ms; Key's last commit is still `0abbcaa` with an empty working
  diff, so k1's bytes are today's bytes)
  3,974 ms on the same bytes, 5.4 percent apart under different load; zero
  sibling binaries; load about 8.7). MEASURED.
- **So census ranks 2 and 3 cost 24 to 26 ms DELIVERED, COMBINED**: that is
  `splitKey∈`'s whole elaboration, which contains both conversions. The
  isolated `t7` arm's 261 ms does not transfer to the delivered setting; the
  delivered figure is ten times smaller. The honest range "0 ms to 522 ms"
  collapses to about 25 ms.
- **The general question the brief asked ("if a profile can hide a charged
  definition by grouping, every not-charged verdict is weaker than it
  reads") has a clean answer: the profiler hid NOTHING here.** The raw table
  carried the row. What hid it was a REPORT'S EXCERPT of the table. The
  practice lesson: a not-charged verdict must be checked against the raw
  `.out` file, never against a report's rendering of it.
- Why the in-master check costs 24 ms where the isolated bridge costs 261 ms
  is not established here. INFERRED candidate: the master's earlier
  definitions (`fromω`, `paramEnv∈`) already forced related `sucIter`
  conversions, and the checker's work is partly shared. I did not read the
  checker. The numbers are measured; the reason is not.

## ATTACK 3: the ladder in a realistic setting

**THE 43-TIMES STEP SURVIVES AT BOTH RUNGS. MEASURED. The ladder transfers
to the delivered sites' own setting within 4 percent.**

`Ladder3.lagda.md`, one agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never
raised, exit 0, agda Total 421,301 ms, wall about 7.1 minutes, zero sibling
binaries at start, load about 7 to 9 across the run (`runs/ladder1.out`).
Under the 30-minute abort line; no heap exhaustion.

| arm | the conversion | ms | its bare twin | ratio |
|---|---|---:|---:|---:|
| `t7r` | depth 2 over iterate base, abstract `T` (a repeat of `[LJ-1.309]`'s t7) | **258** | 261 (t7) | 0.99 |
| `b3` | depth 3, bare | **9,214** | 9,286 (w3) | 0.99 |
| `t3` | depth 3, abstract `T` | **8,962** | 9,214 (b3, same run) | **0.97** |
| `t4` | depth 4, abstract `T` | **402,034** | 419,218 (w4, `[LJ-1.292]`) | **0.96** |

- The abstract stage function is NOT a shield at any depth: `t3` and `t4`
  land 3 and 4 percent BELOW their bare twins.
- The steps in the realistic setting: t2 to t3 multiplies by 41 (219 to
  8,962), t3 to t4 by 45 (8,962 to 402,034). **The super-linear shape R-40
  records holds, and `[LJ-1.309]`'s prize arithmetic was built on real
  rungs.** P-l is answered for this transfer: the hypothesis is now a price,
  at every depth the delivered sites could reach.

### THE `#` SITE'S DELIVERED PRICE (closing attack 1)

`NameCtrl.lagda.md`, the verbatim copy of `src/L/Choice/Name.lagda.md`
(module renamed; diff modulo the name is empty). Wall 2.610 s, exit 0, zero
siblings, load about 7.1. `runs/name-e1.out`: Total 1,667 ms, and
**`_.both`, the where-block holding the `#`-flavored depth-2 conversion at
Name:129-135, is charged 17 ms. MEASURED.** The one site the `sucIter`
filter structurally missed costs SEVENTEEN MILLISECONDS delivered, and its
isolated conversion sits below the 12 ms threshold (`hL2`). It is not a
prize in any arithmetic.

A first cure sketch (`NameCure.lagda.md`, respelling the mono's membership
argument through the library's `ω-next`) does NOT typecheck: it meets the
seam between the library's `∈ₛ` and the project's `∈ˢ` memberships, the
seam `L.Ordinal`'s `#∈ω` exists to bridge (`src/L/Ordinal.lagda.md:248-249`).
Exit 42, `runs/name-e2.out`. **No further attempt, per the brief's "do not
cure it". Nothing is proposed and nothing landed.**

## ATTACK 4: the 90 of 96

- The four `sucIter` files re-derived VERIFIED: 51 occurrence lines in
  StageArith, Bound, Key, EnvSupply. MEASURED.
- **The census's stated REASON is FALSE: "no other master names an iterate at
  all" does not hold, because `#_` is a numeral iterate and ALL 96 masters name
  it in-fence (972 in-fence occurrences). MEASURED.** The clearance survives
  only through the emitter-side argument (above), which `[LJ-1.309]` did not
  make.

## ATTACK 5: the half-cure's self-refutation

**REFUTATED BY MEASUREMENT. The printed half-cure moves the cost at the SAME
depth; it does not multiply it by 42.**

`KeyHalf.lagda.md` is the verbatim copy plus exactly `[LJ-1.309]`'s printed
diff (`:118`'s `T (sucIter 2 σ)` respelled to `T (sucV (sucV σ))`; `diff`
against the control is the module name and that one line). Wall 4.980 s,
exit 0, load about 8.7, zero sibling binaries. `runs/key-e2.out`:

| definition | E1, verbatim | E2, half-cure |
|---|---:|---:|
| `KeyOver._.pair∈` | **237 ms** | not charged |
| `KeyOver.paramEnv∈` | not charged | **242 ms** |
| `KeyOver.splitKey∈` | 24 ms | 24 ms |
| `KeyOver.fromω` | 18 ms | 18 ms |
| `Land.landed` | 14 ms | 14 ms |
| `setSub` | 11 ms | 11 ms |
| Total | 3,761 ms | 3,859 ms |

MEASURED, a controlled pair on identical bytes.

- **The mismatch moves from `pair∈` to its enclosing `paramEnv∈` at the same
  size (237 to 242 ms).** No depth-3 explosion: the file's top charge is 242
  ms, nowhere near the ladder's 9,286 ms.
- **The textual reason, confirmed by the run:** with only `:118` respelled,
  `T-fin`'s first argument at `:115` STAYS `sucIter 2 σ`, so `T-fin`'s
  conclusion stays `T (sucV (sucIter 2 σ))` against `:113`'s
  `T (sucIter 3 σ)`, a DEPTH-1 conversion, the free family. The 42-times
  sentence required ALSO respelling `:115`'s argument, an edit the report
  did not print. INFERRED from the reading; the run confirms no explosion.
- **What survives of `[LJ-1.309]`'s argument:** the half-cure still removes
  nothing (the cost moves, 237 to 242 ms), and the full cure is still a
  vocabulary change. The DO-NOT-FUND verdict does not rest on the refuted
  sentence, but the sentence was presented as "the sentence that makes DO
  NOT FUND correct rather than merely cheap", and it is wrong by a factor of
  about 40 in the direction that mattered to it.

## DD4 AXIS

**AXIS NAMED (C-46): AC-against-GCH**, computed by `ledger.py --reuse` from
`ac_root = "src/L/Model.lagda.md"` (`dev/ledger.toml:170`) and
`gch_root = "src/L/GCH.lagda.md"` (`:204`). A respelling changes seconds and
not lines. My brief's pointer, `ledger.py:50`, lands in the tool's usage
text; the axis is fixed by those two roots and the closure code at
`scripts/measure/ledger.py:389-410`.

- **Closure figures re-derived with the ledger's own regex on the tree at
  HEAD: AC 73 masters, GCH 51, shared 44.** They reproduce `ledger.py
  --reuse` exactly (73/17,197, 51/9,967, 44/7,632, 39.1 percent). MEASURED.
- **`Key.lagda.md` is in NEITHER closure. MEASURED by my own import walk.**
  `[LJ-1.309]`'s claim VERIFIED.
- **The understatement qualification (`dev/ledger.toml:204`): the GCH closure
  is the STATEMENT's, and `sq` is an unsupplied Pi-parameter.** I checked
  whether supplying `sq` could pull `Key.lagda.md` in:
  - `SqShape` is stated in GCH's own vocabulary (`src/L/GCH.lagda.md:44-47`).
  - The natural supplier is the square-law content. `SquareLaw.lagda.md`
    holds ZERO references to `L.Coding` (grep count 0). MEASURED.
  - No `trophy_split` or owed row of the ledger names `Key.lagda.md` or
    `EnvSupply.lagda.md`. MEASURED by grep over `dev/ledger.toml`.
  - Only `KeyRead.lagda.md` and `EnvSupply.lagda.md` import Key, and neither
    reaches either root. MEASURED by the walk.
  **So the qualification does NOT plausibly apply to `Key.lagda.md`: the
  seconds at the three sites are paid ZERO times on the axis today and no
  owed row or supplier cone is set to change that. INFERRED, on the walk plus
  the owed rows; a future wing design could still import the Coding cone by
  choice.**

## THE ABORT CRITERION, ANSWERED BRANCH BY BRANCH (D-1)

| branch fixed before the run | verdict |
|---|---|
| the filter is complete and the tree is clean → UPHOLD and STOP | **DID NOT FIRE CLEANLY.** The filter is NOT complete: `#_` is a second numeral iterate and one depth-2 `#`-flavored site exists (Name:129-135). But no PAID depth-3-or-more site exists in either channel, so the branch's substance, closing the line with a record, holds with the correction recorded |
| a second spelling exists → name it, count its sites, rank by depth, do not cure | **FIRED, and the hit is hollow.** `#_` named; ONE depth-2 site; 17 ms delivered, below 12 ms isolated. The `#` ladder's depth-4 rung is 10,903 ms, 38 times under the `sucIter` ladder's. One cure sketch attempted for measurement, failed on the membership seam, none proposed |
| Condensation's cost has a different mechanism → name it | **NAMED, and it was already on record:** the rebuilt saturation-graph machinery, `SatGraphB.satGraphB` (`:2294`), `SatGraphB.twelveB` (`:2236`), `closedBS` (`:1586`), `[LJ-1.283]`'s triage rows 2 to 4 over `[LJ-1.218]`'s 132.28 s. Not a spelling conversion |
| the 522 ms reconciles to zero | **FIRED WITH A CORRECTION: it reconciles to about 25 ms.** k1.out:26 always carried `splitKey∈` at 26 ms; my E1 reproduces 24 ms. The census is tighter than its author claimed |
| a wall | **DID NOT FIRE.** Longest run 402 s of agda time, wall about 7.1 minutes, exit 0. Cap never raised |

## THE RULES THIS CHAIN EARNED, APPLIED HERE

- **C-42.** `[LJ-1.309]` extended a per-file grep to a whole-tree clearance
  ("no other master can hold the shape at all") on the iterate side. This
  review measured the extension's blind spot: a second iterate exists, one
  site was missed, and it cost 17 ms. The clearance's conclusion survived
  only through an argument the report never made, the emitter-side
  enumeration.
- **C-50.** I profiled before judging every cure claim. The half-cure's
  "42 times worse" fell to a controlled pair; the 522 ms fell to the raw
  profile.
- **C-44.** Applied in both directions: `[LJ-1.309]`'s numbers, `[LJ-1.292]`'s
  excerpted table, and my own brief's "62 percent" (wrong; 71.4).
- **R-41.** Read whole (`dev/LESSONS.md:4247-4334`). Its law says "a level,
  an index or a stage... the SAME FORM the proof term produces". The `#`
  channel is inside the law's letter and outside the sweep's grep; the law
  was right where the grep was narrow.
- **P-l.** Answered at depths 3 and 4 (attack 3) and for the isolated-versus-
  delivered gap (24 ms against 261 ms): a judgement at one site is a
  hypothesis at another, and two of those hypotheses broke on measurement.

## ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-309/lj-1.309-report.md`, read WHOLE as the brief
  requires.** ONE line: section 2.1, "Only `sucIter` builds a numeral stage
  iterate in `src/`. MEASURED." **TAKEN:** the census's three sites, the
  two-grep method, and the t2/b2 transfer, all of which re-derived and held.
  **NOT TAKEN:** the completeness claim, which this review overturns.
- **`agents/tasks/LJ-1-292/lj-1.292-report.md`, read WHOLE.** ONE line: `:23-25`,
  "`KeyOver._.pair∈`... a bounded-formula membership climb with no `sucIter`
  mismatch in it", the sentence `[LJ-1.309]` refuted and my E1/E2 pair
  confirms refuted. **TAKEN:** the ladder, and ABOVE ALL `runs/k1.out`'s
  existence, whose line 26 settles attack 2. **NOT TAKEN:** its section-2
  table AS the profile; it is a selected excerpt of a 42-row file, and that
  distinction is this review's sharpest finding.
- **`agents/tasks/LJ-1-287/lj-1.287-report.md`, sections 2.5 and 4.4 read.**
  ONE line: `:402`, "`src/L/Coding/Key.lagda.md:424-429` CARRIES THE SHAPE.
  UNMEASURED." **TAKEN AS THE SHAPE OF AN ERROR:** a weak reading's false
  positive cost a dispatch, and its false negative (`:118`) is what
  `[LJ-1.309]` then found. **NOT TAKEN:** its 34-line count (32 today).
- **`agents/tasks/LJ-1-289/lj-1.289-report.md`, the diff table read.** ONE
  line: `:92`, "Only the declared level changes, from `sucIter 4 δ` to
  `sucV δ₃`." **TAKEN:** the respelling template that made my E2 and my
  NameCure sketch writable. **NOT TAKEN:** its 488.59 s saving as a
  comparable; P-l forbids it, and `[LJ-1.309]` refused it too, correctly.
- **`archive/dev/TASKS-archived.md`, SHAPE ONLY.** ONE line: `:189`,
  `[L3.32-T154]`, "FOUND, one wall: the depth-6 ordinal witness; cured 631 s
  to 59 s in harness." **TAKEN AS SHAPE:** successor-depth walls are cured by
  restating a spelling, never by sealing, which is why this review tested the
  respellings rather than trust or dismiss them. **NOT TAKEN:** every number;
  they price a retired tree under a different head.

## LITERATURE USED (DD18)

**No mathematical literature bears on a typechecker's cost model for a
spelling.** The question is Agda's conversion checker, not set theory. None
used.

## TWO PRACTICE NOTES FOR THE ORCHESTRATOR (findings, not proposals)

1. **A not-charged verdict must be read from the raw `.out` file.** The
   522-ms mystery existed only because a report's excerpt dropped a 26 ms
   row that the cited run always carried.
2. **If R-41's census is recorded, it must name the iterate CLASS, not the
   token `sucIter`.** `#_` is a numeral iterate in the same sense, present in
   every master. The recorded census should say "explicit chain against ANY
   numeral iterate (`sucIter`, `#`)" and give the emitter-side argument,
   which is what actually closes the tree.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Everything I wrote is in `agents/tasks/LJ-1-311/`:

- `LJ-1.311.md`, the pinned brief, written by the orchestrator before me.
- `lj-1.311-report.md`, this file.
- `Bridge.lagda.md`, the `#`-bridge probe. GREEN, exit 0, wall 13.17 s, after
  one parse-error fix (`runs/bridge1.out`, exit 42).
- `Ladder3.lagda.md`, the depth-3 and depth-4 re-measurement. GREEN, exit 0,
  agda Total 421,301 ms, wall about 7.1 minutes.
- `KeyCtrl.lagda.md` and `KeyHalf.lagda.md`, the controlled pair on
  `src/L/Coding/Key.lagda.md`'s bytes. GREEN, exit 0, walls 4.998 and 4.980 s.
- `NameCtrl.lagda.md`, the Name control. GREEN, exit 0, wall 2.610 s.
- `NameCure.lagda.md`, the cure sketch, written for measurement only. RED by
  the sketch's own design, exit 42 (`runs/name-e2.out`), on the `∈ₛ`
  against `∈ˢ` seam. Kept as the record of the one attempt. Nothing landed.
- `runs/`, eight output files: `bridge1` `bridge2` `bridge3` `key-e1`
  `key-e2` `ladder1` `name-e1` `name-e2`.

**No master edited. No `src/` path written. No `dev/` path written.** I did
not touch `src/Everything.lagda.md`, `agents/tasks/LJ-1-309/`, or any other
task directory. **No commit, no push, no `git checkout .`, no stash, no
reset, no clean. I did not run `make check`.**

**C-12 discipline.** I counted agda binaries with the brief's command
(`ps aux | awk '/libexec.*bin/agda/ && !/awk/' | wc -l`) before EVERY run:
zero before `bridge2`, `bridge3`, `key-e1`, `key-e2`, `ladder1`, `name-e1`
and `name-e2`; one before `bridge1`, so one slot was free. **I ran ONE agda
process at a time**, `GHCRTS="-A64m -I0 -M8g"`, cap never raised, and no run
hit a heap exhaustion.

**Machine load** beside the absolute figures: 9.49/7.67/6.52 at the Bridge
series, 8.69/7.33/6.61 at the Key pair, about 7 to 9 across the ladder run,
7.12/7.16/6.83 at the Name runs. A busy machine throughout. Every comparison
in this report is within one run or between runs on the same bytes, so the
load cancels.

**One census detail corrected in passing (C-44).** `[LJ-1.309]`'s alias
claim, "every `= sucV` line outside EnvSupply binds a chain of depth 1", has
one exception: `Bound.lagda.md:77`'s `β = sucV (sucV σ)`, depth 2. The site
is already among the seven chain lines and is matched-spelled, so nothing
follows. MEASURED: 53 alias lines, exactly one depth-2 alias outside
EnvSupply.
