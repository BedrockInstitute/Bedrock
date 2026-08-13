# [LJ-1.128] Re-measure the DD24 ratio baseline

Status: DONE. `ledger.py --check` is clean.

## 1. Headline

| term | old (2026-08-11) | new (2026-08-13) |
|---|---|---|
| seconds per line | 0.007847 | **0.008793** |
| numerator, cold wall | 133.45 s | **151.11 s**, mean of 5 |
| denominator, in-fence lines | 17,006 | **17,185** |

Run-to-run spread: **5.55 s** over five cold runs (148.56 to 154.11).

The rise is plus 12.05 percent. **A control run shows that almost all of it is
the machine, not the content.** See section 5.

## 2. What the two terms are

`scripts/ledger.py:271-288` (`validate_ratio_baseline`) defines the denominator.

- Root: `ac_baseline_root = "src/Landmarks.lagda.md"` (`dev/ledger.toml:2557`).
- The denominator is the import closure of that root over every tracked
  master, minus `UNCOUNTED` (`scripts/ledger.py:92`: both catalogs).
- Caliber: non-blank lines inside ` ```agda ` fences, read from HEAD
  (`scripts/ledger.py:120-129`).
- The numerator is ONE cold build of the same root, so both terms describe one
  tree (`dev/ledger.toml:2741-2744`).

MEASURED with ledger.py's own functions, at the current HEAD 3619ad4:

- Tracked masters 87. Cone 74 masters, 73 counted.
- Denominator at HEAD: **17,185**.
- Denominator on the working tree: **17,185**. The two are EQUAL.

That equality is load-bearing. A cold build compiles the WORKING tree, while
`count()` reads HEAD. The working tree carries uncommitted work at
`src/L/Condensation/TwelveAgree.lagda.md`. MEASURED: that master is one of the
13 masters OUTSIDE the cone, so the build compiled HEAD content only.

## 3. How I made the build cold

1. `mv _build/2.8.0/agda _build/2.8.0/agda.stash-lj-1.128`. That directory is
   the only project interface store and held 299 interfaces.
2. `rm -rf _build/2.8.0/agda` before each later run.
3. `/usr/bin/time -l env GHCRTS="-A64m -I0 -M8g" agda src/Landmarks.lagda.md`.
4. After the last run: `rm -rf` my fresh cache, then the stash back. MEASURED
   after the restore: 299 interfaces, the count I started with.

How I avoided disturbing the rest of the tree: the restore puts back the
interfaces of the 13 masters outside the cone, which my cone builds never
produced. The next `make check` therefore re-elaborates nothing it would not
have re-elaborated before I started.

The cubical library keeps its 1,092 interfaces in
`/opt/homebrew/Cellar/agda/2.8.0-r3/share/agda/cubical/_build`, outside the
project. My protocol never touched them, and no earlier figure here did either:
a build that re-checked cubical would not return in 133 s.

CALIBER. `ac_baseline_ghcrts` declared `-A64m -I0 -M16g`. C-12 caps a dispatched
agent at 8 GB, so I ran `-M8g` and **wrote the row to match the run I made**.

- MEASURED: peak resident set size 1.18 GiB on every run.
- INFERRED: GHC enables compacting collection only above 30 percent of the
  maximum heap, which is 2.4 GiB at `-M8g`. The cap never binds, so it changes
  no GC decision and the two settings are one instrument on this tree.
- The two flags that DO decide are `-A64m -I0`, and they are unchanged. The
  ledger prices their absence at 22.3 percent (`dev/ledger.toml:2778-2782`).

## 4. The runs

Main series, tree at HEAD 3619ad4, 17,185 lines:

| run | real s | user s | max RSS | instructions | cycles | exit |
|---|---|---|---|---|---|---|
| 1 | 150.24 | 148.67 | 1.18 GiB | 1.9408e12 | 6.0619e11 | 0 |
| 2 | 149.33 | 147.96 | 1.18 GiB | -- | -- | 0 |
| 3 | 154.11 | 151.39 | 1.14 GiB | -- | -- | 0 |
| 4 | 153.31 | 151.48 | 1.18 GiB | -- | -- | 0 |
| 5 | 148.56 | 147.56 | 1.18 GiB | 1.9401e12 | 5.9667e11 | 0 |

Mean 151.11 s. Spread 5.55 s. No run was discarded, per [LJ-0.5]'s rule at
`dev/ledger.toml:2750-2753`: discarding the slow run defines the bar as
page-cache-warm and biases it low, which is the wrong direction for a gate.

Logs: `_build/lj-1.128-run2.log`, `-run3.log`, `-run4.log`, `-run5.log`.

## 5. The control run, which is the real finding

MEASURED with `git diff --name-only f48ffd7 HEAD -- src/`: since the commit
that wrote 0.007847, exactly TWO masters inside the cone changed,
`src/L/Coding/EnvSet.lagda.md` and `src/L/Coding/Sound.lagda.md`. That is
[LJ-1.122]'s generic environment-set, plus 179 in-fence lines. Every other
changed master is outside the cone.

So I built the OLD tree cold, on this machine, on this day. `git worktree add
--detach /tmp/bedrock-lj1128-control f48ffd7`, then ledger.py in that worktree
to confirm its denominator: **17,006, 74 masters, 73 counted**, which
reproduces the recorded figure exactly.

| control run | real s | instructions | cycles |
|---|---|---|---|
| A | 149.06 | 1.9280e12 | 6.0169e11 |
| B | 147.85 | 1.9281e12 | 5.9918e11 |

Control mean **148.46 s** for the tree whose recorded figure is **133.45 s**.

**The identical tree costs 11.2 percent more seconds today.** The machine moved,
not the mathematics.

What the 179 lines really cost, both sides measured on one instrument on one
day:

- Wall: 151.11 against 148.46, plus 2.65 s or 1.79 percent, INSIDE the 5.55 s
  spread.
- Retired instructions, which are sharper than the wall clock: 1.9401e12
  against 1.9281e12, plus **0.62 percent**, for plus 1.05 percent of lines.

P-q again, in the good direction: the added lines check cheaper than the tree's
mean line. The control worktree is removed, `/tmp/bedrock-lj1128-control` no
longer exists, and `git worktree list` shows the same 7 entries as before.

## 6. The machine was NOT quiet, and the brief said it was

MEASURED with `ps -Ao pcpu,comm -r` during the run series:

```
 56.7 GF-Trader Helper (GPU)
 49.1 Bitcoin-Qt
 28.3 WindowServer
 25.8 GF-Trader Helper (Renderer)
 25.2 WebKit WebContent    (three of these, about 25 each)
```

The brief's claim was that no other AGENT runs Agda, and that is true. The
machine itself carried about 2.5 cores of the owner's applications.

It is NOT throttling, and that took measuring:

- Clock 4.02 to 4.05 GHz on every run, computed from cycles over real seconds.
- `pmset -g therm`: no thermal warning, no performance warning. AC power.
  `lowpowermode 0`.
- Instructions per cycle 3.20 to 3.25 today, against an implied 3.57 for the
  2026-08-11 figure. That implied value assumes the clock was the same that
  day; no counter was recorded then, so it is INFERRED.

Lower IPC at an unchanged clock is what memory-bandwidth contention does.

CONSEQUENCE, and the orchestrator should rule on it: **a baseline measured
under load is about 11 percent LOOSE**, and DD24's bar is baseline times 1.15.
A wing module later measured on a quiet machine gets seconds it did not earn. I
wrote the MEASURED figure, because that is what the instrument said and a paper
rescale is exactly what this guard refuses. The normalization is recorded in the
provenance for a reader who needs it: 0.007847 times 151.11 over 148.46 is
**0.007987**.

## 7. The `dev/ledger.toml` diff

98 insertions, 3 deletions. **Exactly three value lines changed**; the rest is
comment and provenance.

```
-ac_baseline_seconds_per_line = 0.007847
+ac_baseline_seconds_per_line = 0.008793
-ac_baseline_lines = 17006
+ac_baseline_lines = 17185
-ac_baseline_ghcrts = "-A64m -I0 -M16g"
+ac_baseline_ghcrts = "-A64m -I0 -M8g"
```

The first two are written together, in one edit each, in one commit, which is
the whole reason the guard exists. The third records the instrument I actually
used; section 3 gives the measured reason the two caps are equivalent here.

NOT CHANGED, and each is deliberate:

- `tolerance = 1.15`. That is DD24's policy and the owner's question.
- `ac_baseline_module_rate = 0.011057` and `ac_baseline_module_lines = 17081`.
  The second caliber is 73 separate builds by `check-ratio.py --recalibrate`.
  It is stale by the same machine factor and by the same 179 lines. The
  provenance now says so. Re-measuring it was not funded and is not what the
  guard reads.
- `compression_seconds_ceiling = 133.4`. It is the closed compression
  campaign's ceiling, and today's instrument cannot produce a number under it.
- `dev/PLAN.md:605` quotes 17,006 in my own task row. The file is modified by a
  sibling agent, so I left it.

## 8. `ledger.py --check` clean

```
$ .venv/bin/python scripts/ledger.py --check
ledger [thresholds SUSPENDED]: AC closure 19,987 against the retired 20,000 cap,
reported and NOT enforced; re-arm is LJ-2.1 ...
ledger: declaration clean; standing 28,611 lines measured over 85 masters
EXIT 0
```

`scripts/lint-prose.py dev/ledger.toml` is also clean.

`scripts/check-ratio.py` needs no separate fix: it CALLS the staleness guard
rather than copying it (`scripts/check-ratio.py:255`), and it reads
`ac_baseline_ghcrts` at `:179` and `:287`, so it now times a wing module with
the same instrument as the baseline.

## 9. Negatives, each marked

- **MEASURED**: no cone master other than EnvSet and Sound changed since
  f48ffd7. `git diff --name-only f48ffd7 HEAD -- src/` lists 11 files and 9 are
  outside the cone.
- **MEASURED**: the uncommitted working-tree master is outside the cone, so the
  numerator and denominator do not describe different trees. Both sums read
  17,185.
- **MEASURED**: the heap cap never binds. Peak RSS 1.18 GiB against a 2.4 GiB
  compaction threshold at `-M8g`.
- **MEASURED**: no heap wall. Every run exited 0.
- **MEASURED**: the CPU is not throttled. 4.02 to 4.05 GHz, no thermal warning.
- **MEASURED**: the 179 new lines are not the cause of the rise. Plus 0.62
  percent instructions and plus 2.65 s against a 5.55 s spread.
- **MEASURED**: the machine was not quiet.
- **INFERRED**: `-M8g` and `-M16g` are one instrument on this tree. It rests on
  the RSS measurement and on GHC's documented 30 percent compaction rule. I did
  not run `-M16g`, because the brief forbids raising the cap.
- **INFERRED**: memory contention explains the 11.2 percent. The clock and the
  instruction count are measured; the CAUSE of the IPC drop is not, and no
  counter from 2026-08-11 exists to compare against.
- **INFERRED**: the 2026-08-11 figure of 133.45 s was taken on the same machine
  with a lighter load. I did not observe that day.

## 10. Two things for the orchestrator to rule on

1. **Accept 0.008793, or re-measure on a quiet machine.** The figure is honest
   for today's instrument and it clears the guard, which unblocks the commit.
   It is about 11 percent loose as a gate.
2. **`ac_baseline_module_rate` is stale by the same factor.** check-ratio.py
   prefers it for a per-module verdict, so a wing module judged today reads
   about 11 percent worse than it is. That is the opposite direction from the
   cone rate, and both errors are live at once.

One more, not mine to act on: `ledger.py --check` now reports the AC closure at
**19,987 against the retired 20,000 cap**, 13 lines under. The cap is demoted
and unenforced, so nothing fails. It is a small number to be sitting on.
