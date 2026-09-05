# LJ-1.282 report: land the seal on A1

tier: opus (in-harness-subagent-mode). Build task. One master edited:
`src/L/Cardinal.lagda.md`. No commit, no push. Written incrementally (C-22).
Every negative is MEASURED or INFERRED, in those words. ASD-STE100 applies.

## 0. LEAD

**The control, measured by me on the landed master: 99.78 s cold. The treated
master: 9.31 s cold. The delta: 90.48 s.** MEASURED, three kept cold runs per
arm, one warm-up discarded per arm, load 5.30 to 7.71. The treated master is
GREEN, exit 0, `--safe`.

**No consumer needed to see inside the seal.** ONE definition looks inside
`w`, and it is the read lemma `w-lt` in the same module. The tree needs
exactly ONE `unfolding` block. Zero outside `src/L/Cardinal.lagda.md`.

| arm | what it is | cold s (mean of 3 kept) | load |
|---|---|---:|---:|
| control | the landed master, `w` transparent | **99.78** | 5.38-7.71 |
| bisect | the master minus `κ-min-at`, `w` transparent, n=1 | 16.37 | 5.86 |
| treated | the master with `w` sealed plus `w-lt` | **9.31** | 5.30-5.69 |

**The abort criterion that fired is the first one: IT LANDS AND THE FILE
DROPS.** No consumer needs the seal opened. No wall. The seal reproduces on
the master.

| figure | control | treated |
|---|---:|---:|
| in-fence non-blank lines | 189 | 204 |
| comment lines / code lines | 44 / 145 | 52 / 152 |
| cold s (mean of 3 kept) | 99.78 | 9.31 |
| rate, s per line | 0.5280 | **0.04562** |
| against the 0.010514 bar | 50.2x | **4.34x** |

## 1. MACHINE AND PROCESS DISCIPLINE

ONE agda process at a time. `GHCRTS="-A64m -I0 -M8g"` on every run. The cap
is never raised. **MEASURED FALSE: a heap exhaustion.** No run went past 30
minutes; the longest run is 103.59 s. No kill.

The harness is `agents/tasks/LJ-1-282/measure.sh`. It deletes the target
interface before every run, so every run is cold for that file. It records
the one-minute load average at the start of each run. The raw rows are
`agents/tasks/LJ-1-282/timings.csv`. Each run keeps its own agda log beside
it, `agents/tasks/LJ-1-282/<arm>-run<n>.log`.

The control and the treated arm both measure the WHOLE master
`src/L/Cardinal.lagda.md`, not A1 alone. This differs from `[LJ-1.281]`,
which measured A1 alone in a probe file. The interface deleted before each
run is `_build/2.8.0/agda/src/L/Cardinal.agdai`. Delivered dependency
interfaces stay cached. No sibling agda process ran during any kept run
(`ps` shows one agda at a time).

## 2. THE CONTROL, MEASURED BY ME

`src/L/Cardinal.lagda.md` as landed, `w` transparent, before any edit.

| run | exit | cold/warm | elapsed s | load |
|---|---|---|---:|---:|
| warm-up (discarded) | 0 | cold | 97.50 | 8.24 |
| kept 1 | 0 | cold | 96.96 | 5.52 |
| kept 2 | 0 | cold | 98.80 | 5.38 |
| kept 3 | 0 | cold | 103.59 | 7.71 |

Mean of the three kept runs: **99.78 s**, range 96.96 to 103.59 s.

**This reproduces the two prior figures.** `[LJ-1.278]` measured the whole
master at 100.57 s (`agents/tasks/LJ-1-278/lj-1.278-report.md:9`).
`[LJ-1.281]` measured A1 alone at 100.50 s
(`agents/tasks/LJ-1-281/lj-1.281-report.md:9-11`). My 99.78 s sits between
them.

## 3. THE TERM, RE-DERIVED ON THE MASTER

The brief asked me to verify the term myself. I bisected the MASTER, not a
probe copy.

**MEASURED. The master without `κ-min-at` costs 16.37 s at load 5.86, exit
0.** I deleted the control file's lines 125 to 138 (the whole `κ-min-at`
definition and its `where` block), ran once, then restored the file from a
byte-identical backup. `shasum` and `git diff` both confirm the restore.

**So `κ-min-at` carries 83.41 s of the 99.78 s, with `w` transparent.** The
brief said 85 of the 100 s. VERIFIED.

**The root is `w`'s transparency, not `κ-min-at` itself, and my own arms
prove it.** Deleting `κ-min-at` leaves 16.37 s. Sealing `w` and KEEPING
`κ-min-at` leaves 9.31 s. **The seal is 7.06 s cheaper than deleting the
consumer-facing theorem.** That figure can only come from the selection
`least = leastOf w` at `src/L/Cardinal.lagda.md:116-117`, which unfolds the
transparent `w` once even when nothing calls it afterwards. MEASURED.

## 4. THE CONSUMER CENSUS, AND P-y'S COUNT

**MEASURED. NOTHING outside `src/L/Cardinal.lagda.md` names
`module LeastCardInjL`.** `grep -rn "LeastCardInjL" src/` returns exactly one
hit, the module header at `src/L/Cardinal.lagda.md:61`.

**MEASURED. The one consumer master imports two names, and neither reaches
`w`.** `src/L/GCH.lagda.md:16` reads
`open import L.Cardinal {ℓ} lem using ( _↪_; IsCardinalL )`. `_↪_` is at
`src/L/Cardinal.lagda.md:47-48` and `IsCardinalL` is at
`src/L/Cardinal.lagda.md:230-233` after the edit. Both sit OUTSIDE
`module LeastCardInjL`.

**MEASURED. `src/Everything.lagda.md:366` imports `L.Cardinal` and names
nothing from it.**

**MEASURED. `κ-min`, `γ-card` and `κ-inj` have no occurrence in `src/`
outside `src/L/Cardinal.lagda.md`.**

**P-y'S TWO COUNTS, SEPARATED.**

| count | value | which definitions |
|---|---:|---|
| definitions that NAME `w` | 3 | `least` (:116-117), `κ-min` (:136-137), `κ-min-at`'s `b<γ` (:152) |
| definitions that LOOK INSIDE `w` | **1** | `w-lt` (:99-101), the read lemma |
| `unfolding` blocks the tree needs | **1** | `opaque unfolding w` at `src/L/Cardinal.lagda.md:97-98` |

**One, not two, and the brief's stop-line was two.** `least` and `κ-min`
name `w` as an ARGUMENT and in an index position. Neither forces the
conversion checker inside it. `κ-min-at` needs the comparison and reaches it
through `w-lt`, so it needs no `unfolding` of its own. This is P-y's exact
claim, and the green check is the measurement.

## 5. THE TREATED MASTER

The edit is 19 insertions and 3 deletions in one file. It takes its shape
from `agents/tasks/LJ-1-281/TreatedOpaque.agda:82-90` and `:141-143`, which
is green.

- **The seal.** `src/L/Cardinal.lagda.md:90-92` now wraps `w` in an `opaque`
  block, under a five-line comment at `:85-89` that names the cause and the
  two figures.
- **The read lemma.** `src/L/Cardinal.lagda.md:97-101` adds `w-lt` in its own
  `opaque unfolding w` block, under a comment at `:94-96`. It states the
  sealed comparison in the ambient membership form and closes by `refl`
  inside the seal. This is R-36's shape (`dev/LESSONS.md:808-814`).
- **The one consumer edit.** `src/L/Cardinal.lagda.md:153-154`: `b<γ` now
  transports along `sym (w-lt b γ-card)`. Its stated type at `:152` is
  unchanged.

**MEASURED FALSE: `κ-min-at`'s exported type changed.** The diff touches
only the body of the local `b<γ`. The signature at
`src/L/Cardinal.lagda.md:140-141` is byte-identical to the control.

| run | exit | cold/warm | elapsed s | load |
|---|---|---|---:|---:|
| warm-up (discarded) | 0 | cold | 9.43 | 5.28 |
| kept 1 | 0 | cold | 9.25 | 5.69 |
| kept 2 | 0 | cold | 9.30 | 5.44 |
| kept 3 | 0 | cold | 9.37 | 5.30 |

Mean of the three kept runs: **9.31 s**, range 9.25 to 9.37 s, spread 1.3
percent.

**MEASURED FALSE: the seal does not reproduce on the master.** It
reproduces. `[LJ-1.281]`'s probe arm gave 9.16 s
(`agents/tasks/LJ-1-281/lj-1.281-report.md:28`); the master gives 9.31 s.
The 0.15 s difference is the A3 and A4 blocks, which the probe arm does not
carry and which `[LJ-1.278]` priced at 2.37 s together
(`agents/tasks/LJ-1-278/lj-1.278-report.md:64`). INFERRED, because I did not
re-bisect A3 and A4 on the treated master.

**The lints pass.** `scripts/lint-agda.py --check src/L/Cardinal.lagda.md`
exits 0. `scripts/lint-prose.py --check src/L/Cardinal.lagda.md` exits 0.
`scripts/weave-i18n.py --check src/L/Cardinal.lagda.md` exits 0. No em dash.
The master carries no `<!--en-->` markers, so DD23's freeze on mathematical
prose is not touched: I wrote code and its own comments only.

## 6. C-40, THE CONSUMER RE-RUN

`src/L/GCH.lagda.md` is the ONE consumer. I re-ran it cold against the
treated master.

| run | exit | cold/warm | elapsed s | load |
|---|---|---|---:|---:|
| warm-up (discarded) | 0 | cold | 1.68 | 5.42 |
| kept 1 | 0 | cold | 1.55 | 5.42 |
| kept 2 | 0 | cold | 1.53 | 5.39 |
| kept 3 | 0 | cold | 1.56 | 5.39 |

**GREEN, exit 0, mean 1.55 s.** `[LJ-1.280]` measured the same master at
1.68 s before the seal (`agents/tasks/LJ-1-280/lj-1.280-report.md:9` and
`:39-41`, three cold runs at load about 6). **The consumer did not get
slower, and it needed no `unfolding`.** MEASURED.

**INFERRED, not measured: the rest of the import closure is unaffected.** I
did not run `make check`; the brief forbids it. The basis is the grep in
section 4: `src/L/GCH.lagda.md` and `src/Everything.lagda.md` are the only
files in `src/` that mention `L.Cardinal`, and `Everything` only imports it.

## 7. THE RATE AGAINST THE BAR

The bar is 0.010514 s per line, which is `ac_baseline_module_rate` 0.009143
times the 1.15 tolerance (`dev/ledger.toml:263-269`; `check-ratio.py:462-464`
is the authority).

| | lines | cold s | s per line | against the bar |
|---|---:|---:|---:|---:|
| control | 189 | 99.78 | 0.5280 | 50.2x |
| treated | 204 | 9.31 | 0.04562 | **4.34x** |

**The master goes from 50.2x the bar to 4.34x, and it gains 15 lines doing
it.** This is P-q exactly: a seconds lever is not a line lever. The 15 lines
are 8 comment and 7 code.

**The rate no longer certifies pure instantiation content (P-m).** At 0.0456
s per line the master is between P-m's parameterized class (near 0.01) and
its instantiation class (near 0.22). P-t explains why: the expensive object
was a transparent presentation in a conversion check, and a sealed carrier
costs nothing extra however concrete it looks (`dev/LESSONS.md:2619-2626`).

## 8. DD4, WITH ITS AXIS

**Axis named (C-46): DD4's own axis is AC-against-GCH**, fixed in code at
`scripts/ledger.py:50`. `src/L/Cardinal.lagda.md` sits in the GCH closure,
and `src/L/GCH.lagda.md` is the root that puts it there
(`dev/PLAN.md:219-222`).

**THE ANSWER: the seal is generic, and the J tower inherits it unchanged.**

The evidence is the sealed block's own name list. `w` and `w-lt` together
name `ordSWO`, `sucV`, `SWO._<∙_`, `⟪_⟫↪`, `_∈ˢ_`, `suc-ord`, and the
module's own parameters `α` and `oα`. **Nothing per-tower appears inside the
seal.** `[LJ-1.278]:190-196` lists `ordSWO`, `sucV`, `leastOf`, `member`,
`fiber` and `⟪_⟫` as the either-tower machinery that transfers verbatim, and
it lists the per-tower objects separately: `isL`, `Lset→isL`,
`ord∈Lset-suc`, `isL-trans` and the carrier `S`.

**Every per-tower object in A1 stays OUTSIDE the seal.** They are `hSucα`
(`src/L/Cardinal.lagda.md:72-74`) and `up` (`:78-80`). A J instantiation
rewrites those two and copies the seal and its read lemma without change.

**INFERRED, not measured: `suc-ord` and `IsOrd` are either-tower.**
`[LJ-1.278]`'s transfer list does not name them. They come from `L.Ordinal`,
which states ordinal facts about `V` rather than about a level predicate, so
a J tower should not need its own copy. I did not build a J instantiation.

**The seconds are the DD4 point.** `[LJ-1.227]` measured A1 as PER-TOWER, so
its check cost is paid once per tower. Before this task that was 100 s per
tower. After it the shared cure makes it 9 s per tower, and the J tower
inherits the cure by copying six lines it would have copied anyway.

**THE P-y WARNING DOES NOT APPLY HERE.** `dev/LESSONS.md:3837-3843` records
that a seal in SHARED upstream machinery improved every master and made the
DD24 ratio WORSE, because the reference side gained more than the judged
side. This seal is inside one master in the GCH closure only. It cannot move
`ac_baseline_module_rate`, because no AC-closure master imports
`L.Cardinal` (section 4). The ratio can only improve. INFERRED: I did not
run `scripts/check-ratio.py`, which the brief keeps outside `make check`
because it costs minutes.

## 9. ARCHIVE USED (DD18)

One line read named per archived file.

- **`agents/tasks/LJ-1-281/lj-1.281-report.md`, read WHOLE.** Line read
  `:146`, "Mean **9.16 s** (three kept). ... Delta from control: **91.34 s**".
  TAKEN: the treated figure I re-derived at 9.31 s on the master, and the
  corrected root (transparency, not fiber extraction).
- **`agents/tasks/LJ-1-281/TreatedOpaque.agda`, read WHOLE.** Line read
  `:90`, `w-lt m n = refl`. TAKEN: the exact shape of the seal and the read
  lemma, and the `transport (λ i → sym (w-lt b γ-card) i)` form at `:142`.
- **`agents/tasks/LJ-1-278/lj-1.278-report.md` sections 0 and 1, plus section
  7 for the DD4 answer.** Line read `:64`, the bisect row "A3+A4+SiteBound,
  no A1 | 119 | 2.37 | 0.020". TAKEN: the 100.57 s whole-master control, the
  98.24 s A1 figure, and at `:190-196` the either-tower transfer list.
- **`dev/LESSONS.md:3803-3847`, P-y read as a FULL entry.** Line read
  `:3806`, "count the consumers that must see INSIDE it, not the consumers
  that NAME it". TAKEN: the two-count method in section 4, and the shared-code
  ratio warning in section 8.
- **`dev/LESSONS.md:808-827`, R-36.** Line read `:811-813`, "add a READ LEMMA
  in its own `opaque unfolding X` block". TAKEN: the read lemma's placement
  and the rule that the seal stays and the surface grows by exactly the
  needed read.
- **`archive/dev/TASKS-archived.md`, SHAPE ONLY.** Line read `:9`, "Nothing
  here is a live task. Read it for history." TAKEN: nothing. WHAT WOULD NOT
  TRANSFER: the file indexes the retired `L3.32-T` series, and this task's
  cure was measured on the live tree this week, so no archived row prices it.
- **`agents/tasks/LJ-1-280/lj-1.280-report.md`.** Line read `:9`, "63
  in-fence non-blank lines (47 code, 16 comment), 1.68 s cold (mean of 3)".
  TAKEN: the pre-seal baseline for the C-40 consumer re-run.

## 10. LITERATURE USED (DD18)

Nothing in the literature governs elaboration cost.

## 11. THE NEGATIVES, CLASSIFIED

- **MEASURED FALSE. A wall.** Longest single run 103.59 s. No heap
  exhaustion. The `-M8g` cap was never raised.
- **MEASURED FALSE. A consumer needs to see inside `w`.** One definition
  looks inside, and it is the read lemma in the same module. `src/L/GCH.lagda.md`
  is green with no `unfolding`.
- **MEASURED FALSE. The seal does not reproduce on the master.** 9.31 s
  against the probe's 9.16 s.
- **MEASURED FALSE. `κ-min-at`'s exported type changed.** Only the body of
  the local `b<γ` changed.
- **MEASURED FALSE. The consumer got slower.** `src/L/GCH.lagda.md` went
  1.68 s to 1.55 s.
- **INFERRED. The seal moves cost to a future consumer.**
  `agents/tasks/LJ-1-281/lj-1.281-report.md:217-220` raised this. Today it
  does not fire, because the only consumer names nothing inside the module. A
  future consumer that must compute `fst κ` would need one more read lemma
  beside `w-lt`, not an unsealing.
- **INFERRED. The rest of the import closure is unaffected.** The basis is a
  grep, not `make check`, which the brief forbids.
- **INFERRED. `suc-ord` and `IsOrd` are either-tower.** They are not on
  `[LJ-1.278]`'s transfer list, and I did not build a J instantiation.

## 12. WORKING TREE, AS MY REPORT DESCRIBES IT

**One master changed: `src/L/Cardinal.lagda.md`,** 19 insertions and 3
deletions, one hunk at the seal and one at `b<γ`.

New files, all in `agents/tasks/LJ-1-282/`:

- `LJ-1.282.md`, the pinned brief.
- `lj-1.282-report.md`, this file.
- `measure.sh`, the timing harness.
- `timings.csv`, every run this task made, one row each.
- `control-run1.log` to `control-run4.log`, `bisect-no-kappa-min-at-run1.log`,
  `treated-run1.log` to `treated-run4.log`, `gch-run1.log` to `gch-run4.log`.

No `src/Everything.lagda.md`, no `dev/ledger.toml`, no `dev/PLAN.md`, no
`src/L/Choice/Name.lagda.md`. The sibling directory
`agents/tasks/LJ-1-283/` was not touched. No commit, no push, no
`git checkout .`, no stash, no reset, no clean. `make check` was not run.

**`git status` shows three untracked paths that are NOT mine:**
`agents/tasks/LJ-1-283/` (the live sibling), `agents/tasks/LJ-1-223/LJ-1.223.md`
and `scripts/tests/test_premises_stated.py`. I did not create or read them.

**The checkers I ran, all exit 0:** `lint-prose.py --check`,
`lint-agda.py --check`, `weave-i18n.py --check`, `check-probes.py --check`,
`check-rule-ids.py`, `check-dd4-stated.py`, `check-dispatch-policy.py`.
