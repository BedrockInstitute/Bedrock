# LJ-1.150 report: place the twelve-row bridge

tier: opus (version `override`). One master changed:
`src/L/Condensation/TwelveAgree.lagda.md`. No commit, no push. No probe was
needed. Every negative is marked **MEASURED** or **INFERRED**.

## 1. VERDICT: GREEN. THE BRIDGE IS PLACED AND THE ONE CONSUMER PASSES

| gate | result |
|---|---|
| `agda src/L/Condensation/TwelveAgree.lagda.md` | **exit 0** |
| `agda src/Everything.lagda.md`, the only consumer | **exit 0** |
| `agda agents/tasks/LJ-1-144/ProbeLJ1144A.agda`, run first | **exit 0** |
| `scripts/lint-agda.py --check` | **exit 0** |
| `scripts/lint-prose.py --check` | **exit 0** |
| `scripts/weave-i18n.py --check` | **exit 0** |
| `scripts/ledger.py --check` | declaration clean |

**What landed**, all in `src/L/Condensation/TwelveAgree.lagda.md`:

- `:31`, the import gained `module SatGraphB`.
- `:47-113`, **top level**: `sixes→twelve` and `twelve→sixes`, the generic
  product re-association. They name no formula, no environment and no carrier.
- `:406-432`, **inside `AbstractFrame`**: `twelve-out` and `twelve-back`, in
  the types `src/L/Condensation.lagda.md:6692-6697` states them.

## 2. THE PROBE STILL ELABORATES. MEASURED, EXIT 0

The brief's first order was to check this before anything else, because
`[LJ-1.147]` sealed `satGraphAt` after `[LJ-1.144]` wrote the probe.

`env GHCRTS="-A64m -I0 -M8g" agda agents/tasks/LJ-1-144/ProbeLJ1144A.agda`:
**exit 0**, **30.44 s real**, 29.12 s user, load 3.29 at start, **4 users**,
780 `.agdai` files present so dependencies were warm.

**The abort criterion "the tree moved enough that the probe no longer
elaborates" did NOT fire.** Nothing was repaired blind, because nothing needed
repair.

## 3. CONSUMER VERDICTS (C-40)

**The consumer set has exactly one member. MEASURED today**, by
`grep -rn "L.Condensation.TwelveAgree" src/`:

| consumer | site | verdict |
|---|---|---|
| `src/Everything.lagda.md` | `:373`, `import L.Condensation.TwelveAgree` | **GREEN, exit 0**, 31.45 s real, 30.01 s user, load 4.45, 4 users |

**`Everything` imports all 85 masters, and the run re-elaborated only
`TwelveAgree` and `Everything` itself** (the run log names those two files and
no other). So the whole import closure answered and nothing else went stale.

**`LowerAgree` and `UpperAgree` are NOT consumers**: `TwelveAgree` imports
them, not the reverse. **MEASURED** at `TwelveAgree.lagda.md:32-35`.

I did not run `make check`. The orchestrator runs it.

## 4. LINES AND SECONDS, WITH THE LOAD AND THE RUN COUNT

### 4.1 Machine state (C-12)

**4 users throughout, and the machine was NOT exclusively mine.** One agda
process at a time, `GHCRTS="-A64m -I0 -M8g"`, **the cap was never raised**, and
**no heap exhaustion occurred**. Load is reported beside every figure. Six agda
runs in total, listed below; the two Python linters are the only other
processes I started, and neither overlapped an agda run.

### 4.2 The runs. SIX, all exit 0

| # | subject | exit | real s | user s | load |
|---|---|---|---:|---:|---|
| 1 | `ProbeLJ1144A.agda` | 0 | 30.439 | 29.12 | 3.29 at start |
| 2 | `TwelveAgree`, **with** bridge | 0 | **28.946** | 27.75 | 4.86 |
| 3 | `TwelveAgree`, **with** bridge | 0 | **29.614** | 28.29 | 6.52 |
| 4 | `TwelveAgree`, **HEAD, no** bridge | 0 | **27.278** | 26.16 | 6.33 |
| 5 | `TwelveAgree`, **HEAD, no** bridge | 0 | **27.059** | 25.86 | 5.83 |
| 6 | `src/Everything.lagda.md` | 0 | 31.453 | 30.01 | 4.45 |

Runs 2 to 5 are a **paired measurement at the master**, not a probe delta. I
deleted `_build/2.8.0/agda/src/L/Condensation/TwelveAgree.agdai` before each,
so each run is the master's own cost with dependencies warm. For runs 4 and 5 I
wrote `git show HEAD:src/L/Condensation/TwelveAgree.lagda.md` into the file and
then restored my version; **the restore is verified**, the working diff after
it is byte-identical to the diff before it.

### 4.3 The delta. MEASURED AT THE MASTER

| figure | without bridge | with bridge | delta |
|---|---:|---:|---:|
| mean real s (2 runs each) | 27.169 | 29.280 | **+2.111 s** |
| mean user s | 26.010 | 28.020 | +2.010 s |
| in-fence non-blank lines | 309 | 397 | **+88** |
| of which code | 302 | 348 | **+46** |
| of which comment | 7 | 49 | **+42** |
| master rate, s per line | 0.08792 | 0.07375 | **−16.1 percent** |

**`[LJ-1.144]` projected about 3.5 s and marked it INFERRED at the master
(P-l). The measurement at the master is 2.11 s, 40 percent BELOW the
projection.** P-l is confirmed in the direction that costs nothing: the probe
figure was a hypothesis and the site was cheaper.

**THE LINE OVERAGE, stated plainly.** The brief projected **about 38 in-fence
lines**. The code delta is **46, which is 21 percent high**. The total delta is
**88**, which is 132 percent high, and the whole excess is **42 comment
lines**. `[LJ-1.144]`'s basis was "the probe's bridge block is 36 non-blank
lines", and the probe's block carries its explanation OUTSIDE that count.
**The basis excluded comments and the project's counting rule includes them**,
so the two numbers measure different things. I did not delete a comment to
improve the figure, because the brief orders code comments written and DD23
does not reach them.

### 4.4 The added content's own rate

**2.111 s over 88 lines is 0.0240 s per line. MEASURED.** That is **2.6x the AC
baseline rate** of 0.009143, and it is **3.7x cheaper than the master it joins**
(0.0879). So the block improves the master's rate while sitting above the bar
on its own.

### 4.5 The DD24 ratio, so the seconds are read correctly

**The twelve wing masters hold 11,526 in-fence lines today with the bridge, and
11,438 without. MEASURED**, `awk` over the ` ```agda ` fences, against the
`gch_wing` list at `dev/ledger.toml:3037-3068`.

**A caveat the ledger's own annotations need:** that list's inline per-master
counts are stale. It records `src/L/Condensation.lagda.md` at "308 in-fence";
the file measures **6,451** today. The membership is what I used; the comments
are not figures.

**The wing's seconds are INFERRED, not measured.** From the recorded 1.91x and
the baseline 0.009143 (`dev/ledger.toml:2730`), the wing rate is 0.017463 and
the wing's seconds are about 199.7. Adding 88 lines and 2.11 s gives
201.8 over 11,526, or 0.017511, so the ratio moves **1.910 to about 1.915**.

**That is plus 0.28 percent, and it is a WORSENING, not a help.** The added
content checks at 0.0240 against the wing's 0.0175 average, so it must drag the
ratio the wrong way, however slightly. **The brief predicted "well under one
percent" and that is what it is.** I claim nothing from it.

`ledger.py --brief` reports **standing 28,635 lines over 85 masters, measured
from HEAD**. My 88 lines are in the working tree only, so that figure does not
yet contain them.

## 5. THE SEAL FORCED NO `unfolding`, AND P-y SAYS WHY

**MEASURED: no `unfolding` was needed, at the probe or at the master.** Neither
run 1 nor runs 2 and 3 carry one, and all three are exit 0.

**P-y's rule is the reason, and the count it orders is zero here.** P-y says
price a seal by the definitions that must look INSIDE the formula, not by the
ones that name it.

- `[LJ-1.147]` sealed **`satGraphAt`** (`src/L/Coding/Graph.lagda.md:203-205`).
- `TwelveAgree` names **`twelveAt`**, which is a plain definition at
  `src/L/Coding/Graph.lagda.md:94` and is **not sealed**. **MEASURED** by
  reading the two `opaque` blocks at `:203` and `:207-208`, which are the only
  two in that file.
- **No definition in `TwelveAgree` looks inside `satGraphAt`.** The one place
  in the tree that opens the seal is `L.Condensation.SatGraphAgree`
  (`src/L/Condensation.lagda.md:6879-6881`), one layer above.

**So the count that prices the seal for this master is 0, and the count that
would have predicted trouble, "names something in the sealed file", is
irrelevant.** P-y is confirmed at a second site.

## 6. WHAT THIS BUYS, AND WHAT IS STILL UNCONSUMED ABOVE IT

**THIS DISCHARGES NOTHING. C-38.** It exports the consumer's type and shortens
the chain by one link. `[LJ-1.144]` said so and I repeat it without softening.

**The instantiation that would make it a discharge does not exist. MEASURED
today** by `grep -rn "AbstractFrame" src/`: the only two hits are my own comment
and the module header. **`AbstractFrame` has zero applications in `src/`.**
Until something applies it at a real `K`, `twelve-out` is produced by a module
nothing runs.

**The whole wing above stays unconsumed, and C-35 keeps firing over all of it.
MEASURED today** by grep:

| level | site | state |
|---|---|---|
| `sixes→twelve`, `twelve→sixes` | `TwelveAgree.lagda.md:78`, `:96` | delivered; used by `twelve-out`/`twelve-back` in the same file |
| `AbstractFrame.twelve-out` / `.twelve-back` | `TwelveAgree.lagda.md:422`, `:428` | **NEW. Produced, and no application exists** |
| `SatGraphAgree`'s two hypotheses | `Condensation.lagda.md:6692-6697` | still unsupplied parameters |
| `LeafAgree` | `Condensation.lagda.md:6913`, applying `SatGraphAgree` at `:6999` | passes them onward; **no importer** |
| `L.BoundedSubset`, its `theorem` at `:1621-1622` | `[LJ-1.146]` measured it | **imported by `src/Everything.lagda.md` ONLY.** Re-measured today |

**So the honest claim is: one link, closed.** The GCH trophy is unwritten, and
nothing in this chain is consumed by anything that proves it.

## 7. DD4: THE BRIDGE IS TEMPLATE, ITS APPLICATION IS GCH-ONLY

**The rule: maximize the code the two proofs share, and write it generic. No
stop-line pushed me toward writing fixed, and I did not write fixed.**

**The two halves have different answers and the split is the point.**

**The re-association IS template content.** `sixes→twelve` and `twelve→sixes`
are stated over twelve arbitrary types at one level. They mention no `Formula`,
no environment, no carrier and no tower. Any future consumer that groups twelve
facts six-and-six reuses them unchanged, on either tower.

**The application is GCH-only, on the Def tower only, and `[LJ-1.144]`'s
literature reading is CONFIRMED rather than refuted.** I read the two cited
lines myself. `dev/literature/devlin-II5.md:375`, row C2, reads "PER-TOWER
content ... **J: the sixteen op-graphs, syntax-free**", and `:253-256` says the
argument "does not require them to have any particular shape, only that some
bounded description with a bound inside the carrier exists". **The twelve rows
are OUR encoding, not Devlin's content.**

**P-w decided the SHAPE, and the shape is where DD4 is paid here.** A module
application copies its body. The 28 lines of projections sit at the top level,
so `AbstractFrame` copies **two one-line applications** per instantiation
instead of 28 lines. `w` is a function argument of `twelve-out`, not a frame
parameter, for the same reason: `twelveB` does not read it, and a telescope
slot would be copied while an argument is not.

**INFERRED, not measured: the saving at future applications.** P-w is the
measured law; `AbstractFrame` has no application, so there is nothing to
measure the saving on. This is exactly `[LJ-1.144]`'s position and I did not
improve on it.

**D-30 answered, because it pulls the other way.** D-30 says price what the
consumer needs, never the general law. The general form here costs **nothing
extra**: the twelve type variables are implicit and are solved by the same
reduction the fixed form would need, and the two functions are 46 code lines in
either shape. **Generality that is free is not the generality D-30 warns
about**, whose measured cost was elaborating parts no consumer reaches.

**D-29 read beside it.** The bridge is a shared layer, so a defect in it would
propagate at the rate the saving does. It is machine-checked in both
directions and its content is projection and pairing only, with no equation and
no transport.

## 8. NEGATIVES, EACH CLASSIFIED

| negative | class |
|---|---|
| the probe stopped elaborating after `[LJ-1.147]`'s seal | **MEASURED FALSE.** Run 1, exit 0, 30.44 s |
| the placement needs an `unfolding` for `satGraphAt` | **MEASURED FALSE.** No `unfolding` anywhere in the edit; runs 2, 3 and 6 exit 0 |
| the placement needs a new master | **MEASURED FALSE.** `TwelveAgree.lagda.md:31` already imported `L.Condensation`; adding `module SatGraphB` to that `using` list compiles |
| the placement forced an edit to `src/L/Condensation.lagda.md` | **MEASURED FALSE.** That file is untouched. `git status` shows one modified file |
| the two `Formula` terms can be made equal | **NOT ATTEMPTED and NOT CLAIMED.** `dev/PLAN.md:548` is true. The bridge is at satisfaction and needs no equation |
| this discharges `twelve-out` | **MEASURED FALSE, by C-38.** `AbstractFrame` has zero applications in `src/` |
| `LeafAgree` or `L.BoundedSubset` now has a consumer | **MEASURED FALSE.** Both are reached only from `src/Everything.lagda.md` |
| the 2.11 s is a probe figure | **MEASURED AT THE MASTER**, four paired runs, not transferred from anywhere |
| the wing seconds and the 1.91x are my measurements | **INFERRED.** I measured the wing's LINES today; the seconds come from the recorded 1.91x and `dev/ledger.toml:2730`, and I ran no wing-wide timing |
| the generic form saves seconds at a future application | **INFERRED.** P-w is the measured law; no application exists |
| the line projection held | **MEASURED FALSE.** 46 code lines against 38 projected, 21 percent high; 88 total, because the basis excluded comments |
| the ratio improves | **MEASURED FALSE in sign.** It worsens by about 0.28 percent, 1.910 to about 1.915 |
| no term could supply `AbstractFrame` at a real `K` | **NOT CLAIMED.** C-36 binds: `[LJ-1.113]`'s 28 pieces are unbuilt, not refuted |

## 9. THE RULES, ANSWERED

- **C-40.** Section 3. The consumer set is one master and it is green. The
  master's own green was never treated as the answer.
- **C-38 as extended.** Section 6, first two paragraphs, and the C-38 note is
  written into the code at `TwelveAgree.lagda.md:418-421` so the next reader
  cannot miss it.
- **C-35.** Section 6. The block still has no real consumer and I say so.
- **P-w.** Section 7. It decided the shape: top level, not inside the frame,
  and `w` as an argument rather than a slot.
- **P-y.** Section 5. Counted the definitions that look inside, and the count
  is zero.
- **P-l.** Section 4.3. The 3.5 s came from a probe and measured 2.11 s at the
  master. I re-measured at the site rather than moving the figure.
- **P-q, P-m, P-n.** The added content checks at 0.0240 s per line, between
  P-m's parameterized band and its instantiation band, which is what pure
  projection at a satisfaction type should cost.
- **C-39.** I checked the brief's own figures rather than repeating them: the
  38-line projection is 21 percent low on code, and the ledger's inline wing
  counts are stale by 6,143 lines on one master (section 4.5).
- **C-12.** One agda process, `-A64m -I0 -M8g`, cap never raised, no heap
  exhaustion, load beside every figure, 4 users throughout.
- **C-22.** This file was a skeleton before the first run and was filled as
  answers landed.
- **C-31 to C-34, C-36, C-37, I-5, D-26.** Read. **C-36** binds section 8's
  last row. **I-5** does not fire: the edit contains no `PT.rec` or `PT.map`
  branch. The others bear on no decision here.
- **D-29, D-30.** Section 7, last two paragraphs.
- **D-1, DD8.** **No probe was built and none was needed.** `[LJ-1.144]`'s
  probe already priced this setting and run 1 re-confirmed it in 30 s, which is
  cheaper than writing a new one. **The widest unmeasured term is unchanged and
  it is not the bridge:** it is `[LJ-1.113]`'s 28 pieces of new content that
  would instantiate `AbstractFrame` at a real `K`.
- **D-10.** The recorded residue is `dev/PLAN.md:548`. `[LJ-1.144]` priced its
  truth; this dispatch spends its proof.
- **DD23.** No mathematical prose was written. The 42 added lines are code
  comments, which the brief orders.
- **DD4.** Section 7.

## 10. ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-144/lj-1.144-report.md`, **read WHOLE**. TOOK the shape
  ruling (`:262-279`), the 3.5 s projection and its P-l marking (`:185-199`),
  the conjunct table (`:122-135`), the no-new-master finding (`:152-157`), the
  C-38 position (`:48-55`) and the literature verdict (`:484-501`).
- `agents/tasks/LJ-1-144/ProbeLJ1144A.agda`, **read WHOLE**. TOOK the two
  projection bodies at `:290-318` verbatim and the consumer's exact types at
  `:328-334`. **Re-ran it before anything else** (section 2).
- `agents/tasks/LJ-1-93/ProbeLJ193A.agda:57-97`, read. TOOK the generic
  `AssocBridge` shape and its comment's reduction argument (`:52-56`).
  **NOT copied:** its twelve formulas are explicit module parameters, which
  forces a consumer to transcribe all twelve conjuncts (`:176-215`). My form
  leaves them implicit and lets unification solve them.
- `agents/tasks/LJ-1-147/lj-1.147-report.md`: **NOT read whole.** I took the
  seal's location and blast radius from `dev/LESSONS.md` P-y, which is the
  same measurement in canonical form, and then verified both against the
  source at `src/L/Coding/Graph.lagda.md:203-208` and
  `src/L/Condensation.lagda.md:6879-6881`. **I record this as taken rather
  than measured by me.**
- `agents/tasks/archive/LJ-1-76/`: **NOT read.** The split it produced is not
  in question here and `[LJ-1.144]` already reported it whole.
- `dev/LESSONS.md`: P-y read WHOLE at `:3704-3744`; C-35 at `:3218-3257`;
  C-38 at `:3445-3500`; C-40 at `:3620-3655`; D-30 at `:3350-3390`; P-w, P-l,
  P-h, P-k, P-m, P-n, C-12, C-22, D-10, R-35, R-38, R-40, I-5 loaded through
  `scripts/rules.py --for build`.
- `dev/ledger.toml:2700-2731` (the baseline and its re-measure) and
  `:3037-3068` (the `gch_wing` membership).
- `dev/PLAN.md:548`, the audit row this dispatch spends.
- `archive/dev/`: **NOT read.** No archived record bears on whether a live
  definition elaborates, and the `D` series is superseded by `DD`.

## 11. LITERATURE USED (DD18)

`dev/literature/devlin-II5.md`, read at `:250-256` and `:373-378`.

**CONFIRMED, in one line as the brief asked: the twelve rows are OUR encoding,
not Devlin's content.** `:253-256` says the argument "does not require them to
have any particular shape, only that some bounded description with a bound
inside the carrier exists", and `:375` classes the bounded Def-step matrix as
**PER-TOWER**, supplied on the J tower by sixteen syntax-free op-graphs.

**And it points exactly where `[LJ-1.144]` said it points**: the bridge's
APPLICATION is Def-tower content, so DD4 is paid by the re-association's form
rather than by the row content. Section 7.

## 12. THE WORKING TREE, AS I LEAVE IT

```
 M src/L/Condensation/TwelveAgree.lagda.md
?? agents/tasks/LJ-1-150/lj-1.150-report.md
```

`git status` also lists `agents/tasks/LJ-1-151/lj-1.151-report.md`, which a
sibling created while I worked. **It is not mine and I did not touch it.**

**One master modified, 95 insertions and 1 deletion.** No commit, no push, no
`git checkout`, no `git stash`, no `git reset`, no `git clean`. No probe was
written. `src/L/Coding/Graph.lagda.md`, `src/L/Condensation.lagda.md` and
`src/Everything.lagda.md` are untouched.
