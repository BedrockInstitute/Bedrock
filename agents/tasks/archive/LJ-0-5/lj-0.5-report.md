# LJ-0.5 report: DD24 baseline, re-measured cold

Task LJ-0.5 measures the AC tree's cold build time. I measure and report. I
change no code. The orchestrator writes the ledger.

## 1. The three cold runs

| Run | Cold seconds | Exit code |
| --- | ------------ | --------- |
| 1   | 138.75       | 0         |
| 2   | 135.82       | 0         |
| 3   | 133.25       | 0         |

Spread: 5.50 s. This is the largest minus the smallest run.

Load average at each run end: 3.49, 4.65, and 3.11. No Agda or GHC process
ran beside the measurement.

## 2. AC lines at HEAD

Standing is 17,595 lines over 78 masters. `scripts/ledger.py --brief` prints
this figure and refuses the endpoint because the remaining rows price the
retired route.

The declared wing is 600 lines. `scripts/ledger.py --check` computes it from
the three files in `ratio.gch_wing`. The AC side is 16,995 lines. That is
17,595 minus 600. The ledger tool computes both figures. I did not count by
hand.

The wing's three files are not in the AC count. They are
`src/V/Collapse.lagda.md`, `src/L/Hull.lagda.md`, and
`src/V/Presentation.lagda.md`. The AC-only figure is 16,995. Do not conflate
it with standing.

The brief names the AC side at 17,149 lines. That number is stale. The tool
now reads 16,995 at HEAD. The drift from the recorded 17,271 is 276, not 122.

## 3. The ratio

Mean cold seconds: 135.94. That is 407.82 divided by three.

Ratio: 135.94 / 16,995 = 0.007999, to six decimals.

Each run's ratio:

| Run | Seconds | Ratio | vs baseline |
| --- | ------- | ----- | ----------- |
| 1   | 138.75  | 0.008164 | +6.12 percent |
| 2   | 135.82  | 0.007992 | +3.88 percent |
| 3   | 133.25  | 0.007841 | +1.92 percent |

The mean ratio is 0.007999. I name the mean as the best-effort number. The
three runs show its noise.

Section 11 supersedes this ratio for DD24. The Everything numerator includes
the wing's seconds. The baseline never built the wing.

## 4. DD24 tolerance

The baseline is 0.007693 s per line. The tolerance is 1.15. The bar is
0.008847 s per line.

The mean ratio of 0.007999 is 3.98 percent above the baseline. Every run is
inside the bar. The rise sits INSIDE DD24's 1.15 tolerance.

The rise is the arithmetic the brief predicts. The tree lost lines at roughly
flat seconds. A ratio must then rise. This is P-q's trap and it is not damage.

Section 11 gives the operative ratio. It is 0.007904, or 2.74 percent above
the baseline. It also sits inside the bar.

## 5. Quiet-machine confirmation

Before the runs I checked for live siblings. The dispatch registry reports
T77 as RUNNING and holding an Agda slot. I checked the recorded pids with
`lsof`. Pid 39084 (T77) and pid 7409 (t192) do not exist. Pid 1354 (t227) is a
macOS system process, ThemeWidgetControlViewService. Pid 4095 is the node
process for this session. T77's final report exists and its log ended on
2026-08-05 with "Done." No Agda, GHC, or codex process runs except this
session. The collaboration harness lists only /root. I judge the machine
quiet for this measurement.

The registry verdict is unreliable in this sandbox. Its `os.kill` liveness
check returns EPERM for any pid outside its view, and `ps` is blocked. The
tool's own D2 note names this hazard. I trusted `lsof` as ground truth.

After the runs I re-checked. No Agda or GHC process exists. The dispatch
registry changed nothing during the measurement. The harness lists only
/root. The registry still reports T77 as RUNNING because its stale record
survives, and the sandboxed `os.kill` check cannot clear it. `lsof` proves
the pid is gone. No sibling started mid-measurement.

Three codex processes from the VS Code extension exist. Their arg0
directories date to 09:29 today. They started before this session. They do
not run Agda. They are not mid-measurement arrivals.

## 6. Exact commands

Cache: `mv _build/2.8.0/agda /private/tmp/lj-0.5-cache-hold/original` before
run 1. Each run regenerates the cache. Before runs 2 and 3 I moved the fresh
cache with `mv _build/2.8.0/agda /private/tmp/lj-0.5-cache-hold/runN`. The
run-3 cache stays in place.

Timing: `env -u GHCRTS /usr/bin/time -p make typecheck`. Output goes to
`/private/tmp/lj-0.5-run1.log`, `-run2.log`, and `-run3.log`. Each log ends
with the exit code. The "real" line is the wall time.

The Makefile exports `GHCRTS ?= -A64m -I0 -M16g`. My shell inherited
`GHCRTS=-M8g`. The `env -u GHCRTS` step removes it. Without this step the
measurement would use the agent cap, not the Makefile default.

Agda: `/opt/homebrew/bin/agda`, version 2.8.0.

Quiet check before each run: `lsof -c agda`, `lsof -c ghc`, `lsof -c codex`,
`uptime`, and `.venv/bin/python .claude/skills/codex-dispatch/dispatch.py
status`.

Rules, mandatory: `.venv/bin/python scripts/rules.py --for recon` and
`.venv/bin/python scripts/rules.py --for probe`. I read every statement.
D-26 is not in play: a timing run builds no well-founded key.

Cold protocol per run:

1. `mv _build/2.8.0/agda /private/tmp/lj-0.5-cache-hold/runN`
2. `env -u GHCRTS /usr/bin/time -p make typecheck`
3. Read the "real" line from the log.

Counting: `.venv/bin/python scripts/ledger.py --brief` for standing, and
`.venv/bin/python scripts/ledger.py --check` for the AC-side figure and the
declared wing. Both read HEAD. I do not count by hand.

Landmarks protocol: `env GHCRTS='-A64m -I0 -M16g' /usr/bin/time -p agda
src/Landmarks.lagda.md`. This is the Makefile's exported GHCRTS value.
Output goes to `/private/tmp/lj-0.5-landmarks-run1.log`, `-run2.log`, and
`-run3.log`. The same cache move and the same quiet checks apply.

## 7. DD4

DD4 is not in play: this task writes no code, and the measurement serves DD4
because the re-priced bar is what stops non-generic GCH content.

## 8. Literature used

`dev/literature/` holds digested mathematics. This is a timing run and no
mathematics bears on it. I read none of it.

## 9. Archive used

`dev/ledger.toml:2443-2467` holds the `[ratio]` block. The protocol
provenance sits at lines 2445-2448. The baseline 0.007693 sits at line 2449.
The denominator 17,271 sits at line 2467. The tolerance 1.15 sits at line
2619. The declared wing list sits at lines 2650-2654. I followed the recorded
protocol, so the new numbers are comparable to the old ones.

`_build/lj-0.8-review.md:224-258` judges the seconds bar. It says the wall
measured 133.19, 133.69, and 132.87, with a spread of 0.82 s. It says seconds,
not the ratio, is the operative gate. It says a flat-seconds compression
raises the ratio by arithmetic, and a rise inside tolerance is expected.

`dev/LESSONS.md` binds timing questions. P-q sits at line 2588 and says a
line lever is not a seconds lever. P-m sits at line 2415 and certifies the
content class by the rate. P-s sits at line 2524 and says slice rates do not
extrapolate to a tree. C-28 sits at line 2750 and says a threshold from a
projection carries its error.

## 10. What I am not sure of

The dispatch registry reports T77 as RUNNING. `lsof` proves the pid is gone.
The registry's `os.kill` check is unreliable in this sandbox. I trusted
`lsof`. The orchestrator may want to clear the stale registry record before
the next measurement.

The host runs GUI applications. I measured no sibling Agda process, which is
the brief's criterion. The ambient load may still add noise. Three runs show
the spread.

The brief names the AC side at 17,149 lines. The ledger's own check now
computes 16,995. The tree moved again after the brief was written. I report
the tool's number.

The three runs decreased in order: 138.75, 135.82, 133.25. The drop may be
OS file-cache warming on the source reads. The interface cache was absent
each run, so every run typechecked cold. I cannot separate the two effects.

The held-aside caches and the run logs live in `/private/tmp`. They sit
outside the repo. The system clears that directory. The regenerated cache
stays in `_build/2.8.0/agda`.

Landmarks run 3 ran under a load spike. The load reached 6.38 at the run
end. The mean includes that run. The spread records it.

`check-ratio.py` measures each wing module cold with warm dependencies. It
runs at `GHCRTS=-M8g`. The AC baseline is whole-cone cold at `-M16g`. The
two calibers differ. The orchestrator should decide whether the wing's
future measurement must match the whole-cone protocol.

## 11. The Landmarks re-measurement: the AC-only numerator

The Everything build includes the wing. The wing sits outside the baseline's
tree. This section re-measures the AC side alone.

**Cone verification.** I computed the import closure of
`src/Landmarks.lagda.md` with the ledger's own import graph and count. The
cone holds 74 masters and 16,916 in-fence lines. The three wing masters are
outside it. The only other master outside it is `src/Everything.lagda.md`,
which has 79 lines. The declaration-based AC side is 75 masters and 16,995
lines. The Landmarks cone is that set minus the root module.

**The three cold runs.** Same protocol as section 6. The cache moved aside
for each run. GHCRTS came from the Makefile. One process ran at a time.
`/usr/bin/time -p` recorded the wall time.

| Run | Cold seconds | Exit code |
| --- | ------------ | --------- |
| 1   | 134.66       | 0         |
| 2   | 132.51       | 0         |
| 3   | 133.94       | 0         |

Spread: 2.15 s. Mean: 133.70 s. The log shows 74 modules checked in each
run.

**The ratio.** Mean seconds divided by 16,916 lines is 0.007904, to six
decimals.

| Run | Seconds | Ratio | vs baseline |
| --- | ------- | ----- | ----------- |
| 1   | 134.66  | 0.007961 | +3.48 percent |
| 2   | 132.51  | 0.007833 | +1.83 percent |
| 3   | 133.94  | 0.007918 | +2.92 percent |

The mean ratio is 0.007904. That is 2.74 percent above 0.007693. The bar is
0.008847. Every run and the mean sit inside it.

**Which figure DD24 should carry.** DD24 should carry the Landmarks ratio:
0.007904 seconds per line over 16,916 lines. The old baseline measured the
AC tree without the wing. The Everything numerator includes wing seconds
that the baseline never built. Its denominator excludes the wing lines.
The new wing content is 582 lines: Collapse 239 plus Hull 343. Presentation
was already in the baseline tree.
That comparison inflates the rise by about 1.2 percentage points. The
Everything-based rise was 3.98 percent. The Landmarks-based rise is 2.74
percent. The Landmarks cone is the AC side by import structure. Its
numerator and denominator describe the same tree. That is the honest
comparison.

**The warm-up question.** Everything's three runs fell in order. Landmarks
did not repeat that shape. Run 2 fell and run 3 rose. Both series had the
slowest first run. Landmarks run 3 rose with a load spike. The first-run
premium is small and partly confounded with load. Discarding run 1 would
define the number as page-cache-warm. That would bias the bar low, which is
the wrong direction for a gate. I do not recommend discarding run 1. Report
all three runs, the mean, and the spread. The mean is the best-effort
number under DD8.

Everything's monotonic drop was likely OS page-cache warming plus falling
load. Landmarks run 1 was already page-cache-warm. The Everything builds
read the same sources minutes earlier. That is why its first-run premium
was smaller.

The Landmarks run-3 cache now sits in `_build/2.8.0/agda`. The Everything
cache from section 6 sits in `/private/tmp` beside the other holds.
