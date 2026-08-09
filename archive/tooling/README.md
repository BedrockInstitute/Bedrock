# archive/tooling: retired scripts

Retired tooling, frozen. Nothing in the live tree imports across this
boundary, and no gate reads it. The rules of the archive are
[archive/README.md](../README.md).

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
