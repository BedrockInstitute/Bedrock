# LJ-1.132 report: salvage what is left in `_build`

Status: **DONE.** Every file has a verdict. Every checker I ran is green.
Nothing is committed. Nothing is pushed.

## 1. The three counts

| Verdict | Files |
|---|---|
| **Deleted** | **24** |
| **Rehomed** | **11** |
| **Archived** | **14** |
| Left in place, now declared | 27 |
| **Inventory total, excluding `2.8.0/`** | **76** |

The brief's glance said "roughly". The measured inventory was **76 files**, not
the 20 that `[LJ-1.130]` reported leaving. That report counted the loose files
at the top level. It did not count `literature/` (23), `probe3/` (15),
`probe/`, `probe2/`, `probes/`, `kits/`, `templates/`, `tools/` or
`usage_data_*/`.

## 2. Sizes, before and after

| Measure | Before | After |
|---|---|---|
| `_build/` total | 187,020 KB (183 MB) | 186,500 KB |
| `_build/2.8.0/`, untouched | 167,128 KB | 167,128 KB |
| **`_build/` excluding `2.8.0/`** | **19,892 KB** | **19,372 KB** |
| `_build/literature/`, untouched | 19,340 KB | 19,340 KB |
| **Excluding `2.8.0/` AND `literature/`** | **552 KB** | **32 KB** |

MEASURED with `du -sk`. The last row is the honest one. **94 percent of the
salvageable content is gone, and 97 percent of what remains is the protected
literature that must not move.** The five surviving files are `.last-gate`, the
watchdog log, the two owner-private CSVs, and the generated `README.md`.

## 3. The citation grep, which decided everything

MEASURED. I ran the brief's grep, then a per-file grep over the 76 files, in
both full-path and basename form, over `dev/`, `agents/`, `scripts/`,
`Makefile` and `REUSE.toml`. The basename pass mattered: it found four files
that the full-path pass called uncited.

**Three findings changed verdicts.**

1. **`agents/reports/lj-1.128-report.md:86` cites four logs in a shorthand
   form.** It writes `` `_build/lj-1.128-run2.log`, `-run3.log`, `-run4.log`,
   `-run5.log` ``. The full-path grep found run2 only. Deleting the other three
   would have broken a live report's evidence.
2. **`dev/LESSONS.md:1012` names `ProbeRudComp.agda` as the provenance of a
   live rule** and says it is "preserved in the session scratchpad". The
   scratchpad was `_build/probes/`.
3. **`dev/ledger.toml` cites three cold profiles as the provenance of standing
   figures** while they sat one `make clean` from deletion.

## 4. The verdict table

### Deleted, 24 files

| File or group | Count | Reason |
|---|---|---|
| `kits/lj-0.4b-Frame.lagda.md`, `lj-0.4f-hierarchy-wiring.diff`, `lj-0.4f-recassembly.lagda.md`, `lj-0.4i-placeBin.lagda.md` | 4 | **Byte-identical duplicates of `archive/kits/`.** MEASURED with `diff -q`: all four IDENTICAL. `[LJ-0.4]`'s closeout archived them on 2026-08-10 and left the `_build/` copies behind. `archive/kits/README.md` states that the `_build/` location "was wrong and the closeout caught it". Nothing is lost. |
| `probe3/*` | 15 | **A probe, and its own report says it is already gone.** `agents/reports/archive/b4e-report.md:35` reads "Standalone mini-probes (`_build/probe3/`, **deleted before finalizing**)". MEASURED: no document cites any of the 15 files, by path or by basename. D-1 makes a probe throwaway and the report holds the verdict. The deletion makes the report true. |
| `dashboard.html` | 1 | **Output of a retired generator, and the generator is archived.** The owner abolished the dashboard on 2026-08-09; `archive/tooling/dashboard.py` holds the code and `archive/tooling/README.md` holds what it did right. Every figure derived from `dev/ledger.toml` and `dev/PLAN.md`, both tracked and live. All 9 citations are historical AND are verification commands (`grep -c '<script' _build/dashboard.html -> 0`), not claims that need the file. `archive/README.md` bars generated files. |
| `lj-1.69-time.py` | 1 | A 33-line wrapper around `scripts/check-timing.py`. MEASURED: **zero** hits anywhere, path or basename. No LJ-1.69 report exists under `agents/reports/`. Reproducible from the canonical tool. |
| `t169-scratch.sh` | 1 | One-off scratch script that copies masters into `/tmp`. MEASURED: zero hits. Exhaust. |
| `tools/agda-watchdog.pid` | 1 | Contained `6518`, a process id from 2026-08-02. Stale runtime state. |
| `.DS_Store` | 1 | macOS clutter. `.gitignore:12` already bars it everywhere. |

### Rehomed, 11 files

| File | New home | Reason |
|---|---|---|
| `l3.32-coldprofile-2026-08-06.txt` | `dev/measurements/` | **Cited by `dev/ledger.toml:2320,2351`, a LIVE document.** It is the provenance of the `measured =` field of a standing figure. |
| `l3.32-coldprofile-2026-08-09.txt` | `dev/measurements/` | **Cited by `dev/ledger.toml:1824`.** The first complete distribution since 2026-08-06; it corrected four standing figures. |
| `l3.32-t256-belowlim-profile.txt` | `dev/measurements/` | **Cited by `dev/ledger.toml:2133`.** The only per-definition profile of the below-limit master. |
| `lj-1.128-run2.log` to `-run5.log` | `dev/measurements/` | **Cited by `agents/reports/lj-1.128-report.md:86`, a LIVE report.** |
| `lj-1.128-controlA.log`, `-controlB.log` | `dev/measurements/` | The raw evidence for that report's headline finding at `:101-106`. Kept with the series they are compared against. |
| `tools/agda-watchdog.sh` | `scripts/` | **Cited by `dev/LESSONS.md:2086`, which is C-12**, the rule every agent is told to work under. A `make clean` deleted the safety mechanism a live rule requires. |
| `lj-1.130-report.md` | `agents/reports/` | The last report written in `_build/`. `[LJ-1.130]` established that reports live in `agents/reports/`. |

**Citations rewritten: 5.** Four in `dev/ledger.toml` (lines 1824, 2133, 2320,
2351) and one in `dev/LESSONS.md` (line 2086). I also repaired
`scripts/agda-watchdog.sh`, which hard-coded an absolute log path; it now
derives the repository root from its own location.

**Citations deliberately NOT rewritten.**
`agents/reports/lj-1.128-report.md:86` still names the old `_build/` path.
`[LJ-1.130]` ruled that a brief and a report are frozen records, corrected in
the next one and never rewritten. This report is that correction, and
`dev/measurements/README.md` records the stale path against the new one.

### Archived, 14 files

| File | New home | Reason |
|---|---|---|
| `t129-baseline.log`, `t132-check.log` | `archive/measurements/` | Cited by `agents/reports/archive/l3.32-t129-report.md`, `-t132-`, `-t139-`. Every citing document is historical. |
| `l3.32-t242-profile.txt`, `-t242-run3.txt`, `-t242-t222-profile.txt`, `-t242b-run1/2/3.txt` | `archive/measurements/` | All six cited by `agents/reports/archive/l3.32-t242-report.md`, historical. |
| `CutProbe.agda`, `StepProbe.agda` | `archive/probes/` | `agents/reports/archive/cut-probe-report.md` cites them **at line numbers** (`:56,60,64,236,248,251`). Such a citation resolves only against the file. |
| `OrderProbe.agda` | `archive/probes/` | `agents/reports/archive/order-probe-report.md:133,136,138`, line-number citations. |
| `ProbeRudComp.agda` | `archive/probes/` | **The provenance of LIVE rule `dev/LESSONS.md` I-2** (`:1012`), plus line-number citations at `agents/reports/archive/p1-report.md:41,80-83`. |
| `ProbeSatSets.agda` | `archive/probes/` | `agents/reports/archive/g2p-report.md:14`, `l3.31-r5probe-report.md:176`. |
| `templates/CodeSetBlock.lagda.md` | `archive/kits/l3.32-t28-CodeSetBlock.lagda.md` | `[L3.32-T28]`'s full trilingual chapter template. `agents/reports/archive/l3.32-t34-report.md:195` calls it "the target shape the surviving chain re-types toward". Written, never landed: that is what `archive/kits/` holds. |

Each new archive directory carries its own `README.md`, following the
precedent that `archive/kits/` and `archive/tooling/` set. Neither of those
has a `dev/ARCHIVE.md` row either; MEASURED, `dev/ARCHIVE.md` indexes retired
MODULES only, and its columns do not fit a log file.

### Left in place, 27 files, now declared

| File or group | Count | Class | Reason |
|---|---|---|---|
| `literature/*` | 23 | `protected` | **Already ruled, at `Makefile:166-179`.** See section 5. |
| `.last-gate` | 1 | `runtime` | Live state, written and read by `scripts/check-tree.py:278`. |
| `tools/agda-watchdog.log` | 1 | `runtime` | See section 6. |
| `usage_data_2026-08-01_2026-08-11/*.csv` | 2 | `foreign` | See section 7. |

## 5. `_build/literature/` must not move, and the ruling already exists

**This is the strongest finding, and it reverses the brief's default.**

`Makefile:166-179` already states the whole lifecycle, in a comment the
`[LJ-0.4]` closeout wrote on 2026-08-10:

> THE FETCHED PRIMARY SOURCES SURVIVE `clean` [...] They cannot be committed,
> because they are copyrighted [...] THE CITATIONS ARE WHAT BREAKS. `[LJ-1.11]`
> cites `dev2.txt` by LINE NUMBER 29 times [...] A re-fetch restores the text
> but not necessarily the same line numbers, because the files are OCR output.

So the directory can be neither deleted nor moved.

- **Not deleted.** `dev/literature/BIBLIOGRAPHY.md:182,191,198`,
  `devlin-II5.md:3,5,574-576` and `geology.md:506` cite it by line number.
  Re-fetching would not reproduce the line numbers.
- **Not moved into `dev/` or `archive/`.** Both are tracked, and `REUSE.toml`
  would stamp every file `SPDX-FileCopyrightText: 2026 Bedrock Institute` and
  `CC-BY-NC-SA-4.0`. These are scans of Devlin (Springer 1984), Jech (Springer
  2003), Jensen and Schindler-Zeman. **Rehoming them would commit copyrighted
  third-party material to a public repository and assert a false copyright.**

`_build/` is the only place in the tree that is outside git by construction.
That is why the literature lives there. The regime now names this as its own
class, `protected`, and the orchestrator's four-class guess had no home for it.

**PROPOSAL for the owner, not done:** the 11 PDFs that nothing cites
(`devlin-ch1.pdf`, `devlin-ch6.pdf`, `jech-front-matter.pdf`, the eight
`jensen-*` files) are 18 MB of the 19 MB, and `dev/literature/primary-sources.md:317-334`
records every fetch URL. They are re-fetchable, unlike the OCR text. **I did
not delete them.** The `.txt` OCR extractions are the load-bearing files and
they are 0.4 MB. Deciding this needs the owner: a re-fetch depends on hosts
that were already Incapsula-blocked and Wayback-dependent in 2026-08.

## 6. The watchdog log, and evidence I am quoting instead of moving

`_build/tools/agda-watchdog.log` is runtime state that `scripts/agda-watchdog.sh`
appends to. It is also the ONLY field record that C-12's backstop has ever
fired. Its three lines, quoted here so a `make clean` cannot erase them:

```
2026-08-02 21:07:26 watchdog started pid=6518
2026-08-03 00:36:20 KILLED agda pid=29704 rss=16880480KB (14g cap)
2026-08-09 00:05:34 KILLED agda pid=7916 rss=16998368KB (14g cap)
```

**Two real kills, both at about 16.9 GB.** Without the backstop, each was a
64 GB machine at risk. `dev/LESSONS.md:2093` records the 2026-08-02 crash that
created the rule; these two lines are the first evidence the cure works.

## 7. Could not classify: one group, and I left it

**`_build/usage_data_2026-08-01_2026-08-11/`, 2 files, 16 KB.**

MEASURED: nothing cites them, by path or basename. They are mode `0600` and
their header is `user_id,start_time_iso,end_time_iso,model,wallet_type,cost,currency`,
with a user id and per-day costs in CNY.

**This is the owner's private billing export, and none of the three verdicts
fits.**

- Not deleted: it is not mine to delete, and it is not a project artifact.
- Not archived: `archive/` is tracked. Archiving would commit a user id and
  spend data to a public repository.
- Not rehomed: same objection.

**What would decide it: the owner's word.** My recommendation is to move it out
of the repository entirely. The manifest classes it `foreign` so no future
agent touches it, but a class is not a fix.

**A live defect the owner should see.** `Makefile:180` runs
`find _build -mindepth 1 -maxdepth 1 ! -name literature -exec rm -rf {} +`.
**`make clean` would delete this directory.** I did not edit the `Makefile`;
it is outside my write scope and a change to `clean` semantics needs a ruling.
The one-line fix, if the data stays:

```make
	find _build -mindepth 1 -maxdepth 1 ! -name literature ! -name 'usage_data_*' -exec rm -rf {} +
```

## 8. One conflict with a stated rule, and I am naming it rather than hiding it

`archive/README.md` reads: "Nothing else belongs here: no live code, **no
probes**, no generated files, no half-maintained second tree." I created
`archive/probes/` anyway, under the brief's instruction to archive what a
historical document cites.

**My reasoning, for the owner to accept or overturn.** That line was written
2026-08-04. The archive has since grown `archive/tooling/` (2026-08-09) and
`archive/kits/` (2026-08-10), and neither is a retired module at its original
path either. `archive/kits/README.md` argues its own departure explicitly. So
the line is already stale against practice, MEASURED by directory mtimes.

**The alternative was deletion, which breaks five line-number citations.**
`archive/probes/README.md` states the conflict in the directory itself. If the
owner prefers the line as written, the cure is to delete the directory and
accept the broken citations, or to widen the line.

## 9. `reuse lint`

**1304 / 1304 files, compliant.** Up from 1269 at `[LJ-1.130]`. Exit 0.

Verified per file with `reuse spdx`, **not by reading the config**, as the
brief required:

| File | Resolved licence |
|---|---|
| `dev/measurements/l3.32-coldprofile-2026-08-06.txt` | CC-BY-NC-SA-4.0 |
| `dev/build-manifest.toml` | CC-BY-NC-SA-4.0 |
| `archive/probes/CutProbe.agda` | CC-BY-NC-SA-4.0 |
| `archive/kits/l3.32-t28-CodeSetBlock.lagda.md` | CC-BY-NC-SA-4.0 |
| `agents/reports/lj-1.130-report.md` | CC-BY-NC-SA-4.0 |
| **`scripts/agda-watchdog.sh`** | **AGPL-3.0-only** |
| **`scripts/check-build-manifest.py`** | **AGPL-3.0-only** |

The split is the owner's three-way principle working: prose and measurements
are CC, scripts are AGPL. **I added no `REUSE.toml` entry and none was needed.**

## 10. THE LIFECYCLE REGIME

### 10.1 The classes, and they came from the inventory

The orchestrator's guess had four classes. **The inventory forced seven**, and
the two extra ones are the interesting result: each exists because real files
had nowhere to go.

| Class | What it is | Delete when | Moves out when |
|---|---|---|---|
| `toolchain` | Owned by an external tool | Never by hand | Never |
| **`protected`** | **Cannot be tracked AND cannot be deleted** | **Never** | **Never; promotion would commit it** |
| `evidence` | A measurement a re-run does NOT reproduce | Never | **Immediately, the moment anything cites it** |
| `working` | Alive while one task runs | When that task's report lands | If the report cites it, it is `evidence` |
| `runtime` | State a live tool writes and reads | When the tool is not running | Never; quote the line into a report |
| `exhaust` | Reproducible by one named command | Any time, by anyone | Never |
| **`foreign`** | **Not the project's to touch** | **Only by the owner** | **Never** |

**`protected` came from `_build/literature/`.** Copyright bars tracking; OCR
line numbers bar re-fetching. The four-class guess had no cell for a file that
can be neither deleted nor promoted, and that is 97 percent of the directory.

**`foreign` came from `usage_data_*/`.** An agent must be told what is not its
to touch. Without this class the next cleanup deletes the owner's data.

**The class that caused the whole backlog is `evidence`, and the fix is that it
has NO resting place in `_build/`.** Three cold profiles sat one `make clean`
from deletion while `dev/ledger.toml` cited them as provenance. The rule is
now: the instant a document cites a measurement, the file leaves `_build/`.

### 10.2 The manifest, and why it is not inside `_build/`

**`dev/build-manifest.toml`**, 7 classes and 10 entries. Each entry is one
glob, one class and a note giving the evidence.

**It cannot live at `_build/MANIFEST.toml` as the brief proposed, and the
reason is mechanical.** `.gitignore:2` ignores `_build/`, and
`scripts/check-probes.py:60-61` fails the gate on any TRACKED file under
`_build/`. A manifest kept there would be untracked, would not survive
`make clean`, and would not survive a fresh clone. **A regime that a routine
command destroys is not a regime** -- which is the exact finding
`archive/kits/README.md` already recorded about the kits.

**`_build/README.md` is GENERATED from the manifest**, by
`scripts/check-build-manifest.py --readme`. It is the copy an agent finds by
`ls`. If `make clean` eats it, one command restores it, and it cannot drift
from the manifest because nobody writes it by hand. That is the property
`archive/tooling/README.md` says the retired dashboard got right: **derive,
never transcribe.**

### 10.3 The checker and its honest limits

**`scripts/check-build-manifest.py`.** It lists every file in `_build/` that
matches no glob. Current run:

```
       2 declared  foreign
      23 declared  protected
       2 declared  runtime
     299 declared  toolchain

every file in _build/ declares a lifecycle.
```

**What it cannot do, stated in its own docstring.** It cannot tell `evidence`
from `exhaust`. Both are text files. The difference is whether re-running a
command reproduces them, and **only the agent who ran the command knows that.**
So it never deletes, never moves, and **never fails a gate**. `AGENTS.md` warns
that a rule claiming more than its checker delivers becomes false safety. This
checker claims exactly one thing: **an undeclared file gets NAMED.**

`--check` returns exit 1 when a file is undeclared, for anyone who wants it in
a script. **I did not wire it into `make check`**, because a red gate for an
un-annotated scratch file would train agents to delete rather than declare.

### 10.4 Where the regime must be stated, so a dispatched agent meets it

**Both places, and the brief section is the load-bearing one.**

1. **`dev/ORCHESTRATION.md:210-215`, "Standing clauses that go in every build
   or probe brief."** That list already carries D-1, D-10 and DD8. It is where
   a rule actually reaches an agent. Proposed clause, for the orchestrator:

   > - **The `_build` lifecycle.** Before you write a file under `_build/`,
   >   add its entry to `dev/build-manifest.toml`: one glob, one class. If no
   >   class fits, say so in your report and stop. A measurement that a
   >   re-run would not reproduce NEVER rests in `_build/`: it goes to
   >   `dev/measurements/` the moment a document cites it.

2. **The brief's `SCOPE (write)` section** (`dev/ORCHESTRATION.md:171`). When
   a brief grants write access to `_build/`, it must name the class the agent
   is expected to produce. A brief that grants the directory without naming
   the class is how the last 76 files got there.

**I did not edit `dev/ORCHESTRATION.md`.** It is outside my write scope.

### 10.5 The `AGENTS.md` line I propose, for the owner's ruling

**I did not edit `AGENTS.md`.** DD19 needs the owner's ruling and a dated
`AGENTS-diff-approved:` trailer.

**One row for the "Where the rules live" table**, after the size-ledger row:

> | **`_build` lifecycle.** Every temporary file declares its class and its expiry when it is created. Seven classes; `protected` and `foreign` may be neither deleted nor tracked. A measurement never rests here: it moves to `dev/measurements/` the moment a document cites it | `dev/build-manifest.toml`, rendered to `_build/README.md` | **PARTIAL.** `check-build-manifest.py` names undeclared files. It cannot tell evidence from exhaust, so it is advisory and never a gate; the declaration is the agent's |

**And one line for the Never list**, which is the shortest statement of the
owner's ruling:

> **Never leave an undeclared file in `_build/`.** It is a temporary folder,
> not a rubbish bin. Declare its class in `dev/build-manifest.toml` when you
> create it, or move it to a permanent home.

**The word cap.** `AGENTS.md` is under the 2,300-word cap at
`scripts/check-dev-docs.py`; `check-dev-docs.py` is green today, MEASURED. The
two blocks above are about 95 words. I did not verify the post-edit count,
because I did not make the edit.

## 11. Every negative, marked

- **MEASURED.** Nothing cites `probe3/*` (15 files), `lj-1.69-time.py`,
  `t169-scratch.sh`, `agda-watchdog.pid`, `.DS_Store`, or the two usage CSVs.
  I ran a per-file grep in full-path and basename form over `dev/`, `agents/`,
  `scripts/`, `Makefile` and `REUSE.toml`.
- **MEASURED.** The four `_build/kits/` files are byte-identical to
  `archive/kits/`. `diff -q` reported IDENTICAL for all four.
- **MEASURED.** `archive/kits/` and `archive/tooling/` have no `dev/ARCHIVE.md`
  row. I grepped `dev/ARCHIVE.md` for both names; the only hits are module rows
  whose prose contains the word "probe".
- **MEASURED.** `scripts/check-probes.py:60-61` fails on any tracked path
  starting with `_build/`. I read the function.
- **INFERRED.** That the 11 uncited literature PDFs are re-fetchable. The URLs
  are recorded, but `primary-sources.md:323-326` says Project Euclid was
  Incapsula-blocked and chapters came from Wayback captures. **I did not test a
  re-fetch**, so this is a hypothesis, not a price (P-l). It is why I left them.
- **INFERRED.** That deleting `dashboard.html` costs nothing. Its generator is
  archived and its inputs are tracked, but I did not run the archived generator
  to confirm it still renders.
- **MEASURED.** `make clean` would delete `_build/usage_data_*/`. I read
  `Makefile:180`; the `! -name literature` predicate is its only exemption.

## 12. Checkers I ran

| Command | Result |
|---|---|
| `scripts/lint-prose.py --check` | **exit 0** |
| `scripts/check-probes.py` | exit 0, 1288 tracked files |
| `scripts/check-tree.py` | exit 0, 87 masters |
| `scripts/check-rule-ids.py` | exit 0, 141 lessons, 66 decisions |
| `scripts/check-dev-docs.py` | exit 0, 6 subchecks |
| `scripts/check-task-index.py` | exit 0, 434 codes |
| `scripts/ledger.py --check` | exit 0, standing 28,617 unchanged |
| `scripts/check-build-manifest.py` | **exit 0, every file declared** |
| `reuse lint` | **exit 0, 1304 / 1304** |

I did not run `make check`. I did not run Agda. I did not touch `_build/2.8.0/`
or anything under `src/`.

## 13. State of the working tree

**Nothing committed. Nothing pushed.** `git status --short` shows 17 entries.

Mine: `archive/kits/README.md`, `dev/LESSONS.md`, `dev/ledger.toml` modified;
`archive/measurements/`, `archive/probes/`, `dev/measurements/`,
`dev/build-manifest.toml`, `scripts/agda-watchdog.sh`,
`scripts/check-build-manifest.py`, `archive/kits/l3.32-t28-CodeSetBlock.lagda.md`,
`agents/reports/lj-1.130-report.md` and this report, new.

**Not mine.** `dev/PLAN.md`, `agents/briefs/LJ-1.131.md`,
`agents/briefs/LJ-1.133.md` and `agents/reports/lj-1.131-report.md` changed
during my run. I touched none of them, and I read nothing under `src/` or
`dev/literature/` beyond `BIBLIOGRAPHY.md` and `primary-sources.md`.

## 14. DD4

**Nothing in this task touched a proof, so DD4 had no line to share.** The
task was a directory salvage and a regime. The one place the DD4 instinct did
apply is the regime itself: the classes are stated once, in
`dev/build-manifest.toml`, and `_build/README.md` is DERIVED from them rather
than restating them. A second hand-written copy of the classes would have been
the documentation equivalent of writing it fixed.

## 15. ARCHIVE USED

- `agents/reports/lj-1.130-report.md`, read whole (now at
  `agents/reports/lj-1.130-report.md:1-239`). Took: the count of what was
  left (`:35-37`), the licence principle (`:41-47`), and the `make clean`
  hazard at `:214-218`, which is what made me check `Makefile:180` first.
- `archive/README.md:1-14` (what belongs in the archive) and `:44-49` (frozen),
  `:70-75` (licensing). The `:12-14` line is the conflict in section 8.
- `archive/kits/README.md:1-30`. Took: the reason kits left `_build/`, and the
  `<task>-<name>` naming that `l3.32-t28-CodeSetBlock.lagda.md` follows.
- `archive/tooling/README.md:1-48`. Took: that `dashboard.py` is archived, and
  "derive, never transcribe", which is why `_build/README.md` is generated.
- `archive/dev/` listing only, to confirm the archive's shape.
- `dev/ARCHIVE.md:1-40`, to confirm its columns are module-specific and that a
  log file has no row there.
- `REUSE.toml`, read whole. Took: `path = "**"` default AGPL, the
  `src/docs/agents/dev` CC override at the `[[annotations]]` block, and the
  `archive/**` override.
- `dev/LESSONS.md` **D-1** (via `rules.py --for rewrite`), and **C-30 gate 9**
  at `:1828-1833`, which is the measured statement that `_build/` does not
  preserve anything.

## 16. LITERATURE

**Nothing in the mathematical literature governs a build directory.**

`dev/literature/BIBLIOGRAPHY.md` was read whole, and it decided section 5.
Entries 20, 21 and 22 (`:180-201`) record the second-round fetches and name
`_build/literature/dev2.txt`, `jech13.txt` and `devlin-ch2.pdf` as their
sources. `dev/literature/primary-sources.md:317-334` lists every fetched file
and its URL. **The digested notes under `dev/literature/` are tracked; the raw
fetches under `_build/literature/` are not, and cannot be.** That is the
distinction the brief asked me to state before moving anything, and it is why
I moved nothing.
