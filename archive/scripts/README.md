# archive/scripts: retired scripts

Retired tooling, frozen. Nothing in the live tree imports across this
boundary, and no gate reads it. The rules of the archive are
[archive/README.md](../README.md).

## The probe lifecycle, retired 2026-08-13, the day it was written

**What it was.** `check-probes-lifecycle.py` is `scripts/check-probes.py` as
`[LJ-1.138]` left it. On top of the never-commit gate it carried a whole
lifecycle: `--stale` gave every probe under `src/` one of four verdicts (HELD,
EVIDENCE, NAMED, ORPHAN), `--sweep` archived and deleted by those verdicts,
`--gate` failed `make check` while a finished probe waited, `--index`
regenerated the evidence table in `archive/src/2026-08-13-probe-sweep/README.md`, and a 24 hour
floor delayed the one irreversible operation. `test_probe_lifecycle.py`, 55
checks, was its suite.

**Why it went.** The owner ruled on 2026-08-13 that a probe pairs one-to-one
with its report, lives beside it in `agents/tasks/<TASK>/`, is tracked, and is
never deleted. **A rule for when to delete a probe has nothing left to decide.**
It is retired as a mechanism whose problem was dissolved, not as a failure.

**What it did right, from measurement rather than praise.**

1. **Every test could only ADD a hold, and none could release one.** The three
   live-task tests were unioned on purpose, so a test that went stale
   over-held. **The asymmetry is the design**: over-holding costs disk, and
   under-holding killed two agents on 2026-08-05. Any future rule that decides
   whether a file may be destroyed should be built this shape.
2. **It refused to separate two classes its test could not separate.**
   `[LJ-1.133]` measured that the prose detector distinguishing NAMED from
   EVIDENCE had been fitted to its own counterexamples, so its recall was
   unknown. The tool took the recoverable side and archived both. **A checker
   that states its own recall limit in its docstring is rarer than it should
   be.**
3. **It read "a task is live" off files rather than off a clock.** The clock it
   replaced was the file's mtime, and mtime failed in BOTH directions: a probe
   written at the start of a three-hour task aged out while the agent needed
   it, and a finished task's probe stayed protected for six hours after it was
   dead. MEASURED 2026-08-13: the mtime rule called all 14 probes in `src/`
   FRESH while all 14 tasks were closed with their reports written.
4. **The archive index was DERIVED, never transcribed.** `--index` rebuilt the
   257-row table from the directory, so it could not drift from the files it
   described.

**What it got wrong, and the lesson is live.** `--staged` read
`git diff --cached --name-only --diff-filter=ACM`, and **`ACM` does not include
a rename.** MEASURED 2026-08-13 at `[LJ-1.141]`: 257 staged probe renames, and
the filter reported ZERO of them. The hole was harmless while probes were
untracked, because a probe had nothing to be renamed FROM. It was live the
moment probes became tracked. **The live script now uses `ACMR`.** Anyone
reusing this code inherits the bug.

**Where it was last green.** `scripts/tests/test_probe_lifecycle.py` passed
55 / 55 standalone on 2026-08-13, hours before the retirement. Under `make test`
it was never reached that day: `test_dev_docs.py` was red on an `AGENTS.md` word
count while a sibling was editing it.

**What would make it worth a second look.** A ruling that puts a class of file
back on a delete-or-keep footing. The union-of-holds shape, the
recall-limit docstring and the derived index are the reusable parts. **Do not
revive the `ACM` filter.**

## The dashboard generator, retired 2026-08-09

**What it was.** `dashboard.py` generated `_build/dashboard.html`, a
self-contained page with inline CSS and no JavaScript, built from the
canonical data in `dev/ledger.toml` and `dev/PLAN.md`. It was the owner's
status board. `check-dashboard.py` reported whether the page was stale
against its sources, informationally and never as a gate.
`test_dashboard.py` was its regression suite.

**Why it went.** The owner abolished the mechanism on 2026-08-09. It is
retired as tooling, not as a failure.

**What it did right, from measurement rather than praise.**

1. **It was GENERATED, never hand-written.** Every figure came from
   `scripts/ledger.py` by subprocess, so the board could not drift from the
   ledger the way a hand-maintained status page does. Any replacement should
   keep that property: derive, never transcribe.

2. **It refused to guess.** Each panel had a `no_data(...)` path. When
   `ledger.py` could not run or `dev/ledger.toml` would not parse, the panel
   said the data was unavailable instead of rendering a plausible number.
   That is the harder half to get right and it is worth copying.

3. **The output was one file with no network dependency,** so it opened from
   a filesystem path with no server and no build step.

**What it got wrong, and the lesson is live.** It parsed `ledger.py`'s stdout
with a regex anchored at position zero. On 2026-08-09 a threshold-suspension
banner was added to that stdout and `make dashboard` crashed with a
`ValueError` for a full day, until `[LJ-0.1]` found it. The banner now goes to
stderr, and `scripts/ledger.py` carries a comment at that site saying why.
**A tool that machine-reads another tool's stdout has made that stdout an
API.** Anyone who reuses this code inherits that contract.

**Where it was last green.** The commit that archived it; `make dashboard`
had been repaired earlier the same day and rendered cleanly before the move.

**What would make it worth a second look.** A request for a generated status
board. The panel structure, the `no_data` discipline and the ledger-derived
figures are the reusable parts. Do not revive the stdout parsing: give
`ledger.py` a `--json` mode instead.
