# LJ-1.195 report: a consistency audit of `AGENTS.md` against `dev/`, by document rank

tier: pi (deepseek-subagent-mode), model `deepseek-v4-flash`.

## 0. LEAD

**FOUR live contradictions and one that was FIXED during this audit. The most
severe live one is the DD4 enforcement account: `AGENTS.md`, the DD4 row and
`dev/ORCHESTRATION.md` all say DD4 has no checker and that repetition is its
only enforcement, while `scripts/check-dd4-stated.py` gates in `make check`
and fails a brief without a `## DD4` heading.**

**The trap the brief named is no longer live.** `AGENTS.md:105` and
`AGENTS.md:137` said reports and probes live in `agents/reports/` and briefs
in `agents/briefs/`. Commit `5a4b295` (2026-08-14 10:47:51) fixed both rows to
`agents/tasks/` with a dated `AGENTS-diff-approved: 2026-08-14` trailer. The
fix landed two minutes after this brief was written (10:45:35). I verified the
fix holds against the world. It is a verified-fixed item, not a live
contradiction.

## 1. THE FINDINGS, RANKED BY COST

### F1. DD4's enforcement account is stale in three documents against a checker that gates. MEASURED

**Side A, `AGENTS.md:21-23`:** "It has NO metric and no checker by the
owner's decision, so it is stated in EVERY brief and answered in every return,
and that repetition is its only enforcement."

**Side B, the world:** `scripts/check-dd4-stated.py` exists, is wired into
`make check` (`Makefile:36`, `Makefile:132-133`), and fails any brief without a
`## DD4` heading. Its docstring is explicit that it is a gate, not a census
(`scripts/check-dd4-stated.py:1-8`).

**Side C, the same stale claim in two other rule documents:**
- `dev/ORCHESTRATION.md:192-193`: "There is no shared-line count and no
  checker, because a count would be gamed the moment it gated anything".
- `dev/ORCHESTRATION.md:210`: "Nothing mechanical checks it, which is
  exactly why it is repeated."
- The DD4 row (`dev/PLAN.md:247`) says "there is no threshold and no
  pass-or-fail, and there never will be", and its enforcement paragraph names
  the ORCHESTRATION clause, the section 5 clause and the return audit, but
  does not name `check-dd4-stated.py`.

**Rank verdict:** `AGENTS.md` is rank 1, so it must change. The DD4 row is
rank 2 and is also behind the checker.

**World verdict:** the world has a checker. `check-dd4-stated.py` exists,
runs in `make check`, and passes or fails a brief on the heading. `AGENTS.md`
and `ORCHESTRATION.md` are wrong about the world; the DD4 row's "no
pass-or-fail, and there never will be" now admits two readings, because a
pass-or-fail gate on the heading exists. This is the no-clean-resolution kind
the brief names as the most valuable.

**Cost:** an agent or orchestrator told "no checker, repetition is its only
enforcement" believes a brief without a DD4 section passes every gate. It
does not: `make check` fails it. The wrong side costs a red gate the reader
was told cannot exist, and hides the checker from everyone who reads the rule
documents instead of the scripts.

### F2. "make check ... runs every checker in scripts/README.md" is false in both directions. MEASURED

**Side A, `AGENTS.md:60-61`:** "It typechecks the masters, then runs every
checker in [scripts/](scripts/README.md)."

**Side B, the world:** the `check:` target (`Makefile:36`) runs `check-fences.py`
and `check-dd4-stated.py`, which have NO section in `scripts/README.md` (grep
for both names finds nothing). And `scripts/README.md` documents checkers that
are deliberately NOT in `make check`:
- `check-timing.py` (`scripts/README.md:538`), the only gate that can fail a
  module for being expensive, "Suspended as a gate by DD5; it reports"
  (`scripts/README.md:544`)
- `check-sources-read.py` (`scripts/README.md:549`): "An audit aid, not a gate;
  exit 0 always"
- `check-ratio.py` (`scripts/README.md:621-622`): "It is NOT in `make check`"
- `check-archive-cited.py` and `check-unbound-hyp.py`: ADVISORY
  (`Makefile:137`, `scripts/README.md:354`)
- `deletion-test.py` and `ledger.py --reuse`: not in `make check`
  (`scripts/README.md:152,186`)

**Rank verdict:** `AGENTS.md` must change.

**World verdict:** the Makefile matches the world. `AGENTS.md` overclaims: it
tells a reader that the commit gate covers checkers the gate deliberately
excludes.

**Cost:** a build agent that touched a master believes `make check` runs the
timing gate and the ratio gate. It does not. `dev/ORCHESTRATION.md:224-231`
warns: "if the orchestrator does not run it at the return, nobody does." The
wrong side costs a skipped gate: an expensive module ships unchecked.

### F3. ORCHESTRATION narrows DD4's enforcement from three points to one. MEASURED

**Side A, `dev/ORCHESTRATION.md:189-190`:** "DD4 GOES IN EVERY BRIEF,
WHATEVER THE KIND, AND THIS CLAUSE IS ITS ONLY ENFORCEMENT."

**Side B, the DD4 row (`dev/PLAN.md:247`):** "Enforcement: the standing brief
clause in `dev/ORCHESTRATION.md` section 3, which fires on every task kind;
the route-planning clause in section 5; and the return audit in section 6,
which rejects a build that chose fixed without saying so."

**Rank verdict:** the lower document (`dev/ORCHESTRATION.md`, rank 3) must
change. The DD is rank 2.

**World verdict:** the DD4 row's three enforcement points are the true ones.
The return audit in `dev/ORCHESTRATION.md` section 6 rejects a fixed build
that did not say so; that is a real enforcement point the "only enforcement"
claim hides.

**Cost:** a reader of the ORCHESTRATION clause believes the return audit does
not enforce DD4. A fixed build that did not say so then ships past the audit.

### F4. The trap: FIXED during this audit, verified. MEASURED

**What the brief expected:** `AGENTS.md:105` said live reports live in
`agents/reports/`, older ones in `agents/reports/archive/`, every brief in
`agents/briefs/`; `AGENTS.md:137` told an agent to write its probe in
`agents/reports/<TASK>/`. None of those directories exists.

**What happened:** commit `5a4b295` fixed both rows to `agents/tasks/` and
`agents/tasks/<TASK>/` at 10:47:51 on 2026-08-14, two minutes after this
brief was written. The commit carries the `AGENTS-diff-approved: 2026-08-14`
trailer, which `scripts/check-agents-guard.py` requires.

**Fix verified:** current `AGENTS.md:105` says "both live in ONE directory per
task, `agents/tasks/<CODE>/`, beside that task's probes"; current
`AGENTS.md:137` says "Write it in `agents/tasks/<TASK>/`, beside your brief
and your report". This matches `dev/PLAN.md:249` (DD8), `agents/README.md`,
`dev/LESSONS.md` D-1, `dev/ORCHESTRATION.md` and `bedrock.agda-lib`.

**World verdict:** the world matches the fixed text. The lower documents were
right; `AGENTS.md` was stale, and the rank-1 document changed to match.

**Cost had it stayed live:** an agent writing to `agents/reports/` would have
produced a dead dispatch and a lost record. It is fixed; nothing costs now.

### F5. DD18's LITERATURE half is absent from AGENTS.md's return rule. INFERRED

**Side A, `AGENTS.md:163-164`:** "Every brief carries an ARCHIVE section
naming what may bear on the task; every return carries an ARCHIVE USED
section naming what it read and took, at `file:line`."

**Side B, the DD18 row (`dev/PLAN.md:255`):** the LITERATURE half is "the same
mechanism for a second corpus"; "a return that arrives without both USED
sections is sent back." `dev/ORCHESTRATION.md` section 3 states the same.

**Rank verdict:** `AGENTS.md` must change (rank 1).

**World verdict:** `dev/PLAN.md` and `dev/ORCHESTRATION.md` match the world:
every return must carry both USED sections. `AGENTS.md` states only the
ARCHIVE half.

**Cost:** an agent that reads only `AGENTS.md` writes ARCHIVE USED but not
LITERATURE USED, and its return is sent back. A wasted dispatch.

## 2. EXAMPLES IN BOTH DIRECTIONS

- **A lower document violating a DD:** `dev/ORCHESTRATION.md:190` calls its
  clause DD4's "ONLY ENFORCEMENT", while the DD4 row (`dev/PLAN.md:247`)
  names three enforcement points. That is F3 above.
- **A DD violating `AGENTS.md`:** the DD8 row (`dev/PLAN.md:249`) says a probe
  is committed in `agents/tasks/<TASK>/`, contradicting `AGENTS.md:137` as it
  read before commit `5a4b295`. The DD was right about the world; `AGENTS.md`
  was stale and changed to match. That is F4 above.

## 3. SEARCHES RUN

- `agents/reports`, `agents/briefs`, `agents/tasks` across `AGENTS.md`,
  `dev/`, `agents/README.md`, `bedrock.agda-lib` (the trap, both spellings).
- `no checker`, `no shared-line count`, `Nothing mechanical checks it`,
  `repetition is its only enforcement`, `no pass-or-fail` across `AGENTS.md`,
  `dev/PLAN.md`, `dev/ORCHESTRATION.md`, `scripts/` (F1, F3).
- `runs every checker`, `NOT in make check`, `deliberately NOT`, `not a gate`
  across `AGENTS.md`, `Makefile`, `scripts/README.md` (F2).
- `LITERATURE USED`, `ARCHIVE USED`, `LITERATURE` across `AGENTS.md`,
  `dev/PLAN.md`, `dev/ORCHESTRATION.md` (F5).
- `git log -- AGENTS.md` and `git show 5a4b295` (F4, the mid-audit fix).
- `265` against `archive/dev/TASKS-archived.md` row count (verified: 265 data
  rows, one header).
- `52 frozen briefs` against the briefs read by `scripts/agents_tree.py`
  (verified: 52 briefs carry an old tier version).
- `P-l` in `dev/LESSONS.md` (verified: the heading is the stage-type law and
  its body carries "A CURE DOES NOT TRANSFER BY ANALOGY", so `AGENTS.md:130`'s
  citation resolves).
- DD4 heading census via `scripts/check-dd4-stated.py` (88 of 100 live briefs
  state DD4, 12 frozen pre-epoch).

## ARCHIVE USED (DD18)

- `AGENTS.md` WHOLE, current working-tree text after commit `5a4b295`, and
  the pre-fix text quoted in the brief; took the live findings.
- `dev/PLAN.md` section 3 WHOLE, all 19 DD rows; took DD4's enforcement
  paragraph (F1, F3), DD8's probe home (F4), DD18's LITERATURE half (F5).
- `dev/ORCHESTRATION.md` WHOLE; took the DD4 clause at section 3 (F1, F3) and
  the check-timing exclusion at section 3 (F2).
- `dev/LESSONS.md` C-12 and P-l; took the heap-cap and citation checks.
- `agents/tasks/LJ-1-187/lj-1.187-report.md` WHOLE; its four canonical-twice
  fixes were checked and hold (ORCHESTRATION:322 now points instead of
  restating; PLAN:487, 133 and 348 point instead of restating). Not re-reported.
- `agents/tasks/LJ-1-183/lj-1.183-report.md` WHOLE; F2 (struck PLAN section)
  and F3 (head names in ORCHESTRATION) are fixed; F4 (DD4 lapses) is now
  gated by `check-dd4-stated.py`; F5 (DD25 rows) is fixed; F6 is history.
- Commit `5a4b295` body WHOLE; took the F4 fix and its DD19 trailer.
- `scripts/check-dd4-stated.py` WHOLE; took the gate's existence and scope
  (F1).
- `scripts/README.md`, `Makefile`, `scripts/check-rule-ids.py`,
  `scripts/weave-i18n.py`, `scripts/i18n_markers.py`, `scripts/lint-prose.py`,
  `scripts/check-agents-guard.py`; took the enforcement facts for F2 and the
  table-row checks that came back clean.

## LITERATURE (DD18)

Not this task's subject.
