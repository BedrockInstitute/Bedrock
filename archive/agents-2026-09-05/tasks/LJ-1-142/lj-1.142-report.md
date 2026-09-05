# LJ-1.142 report: one directory per task, holding its brief, its report and its probes

STATUS: **DONE.** The merge landed. **547 task directories** hold every brief, every report and
every probe. **All fourteen consumers pass**, and the brief named thirteen: I found a
fourteenth. **Nothing committed. Nothing pushed. Nothing deleted.**

Every negative below is marked **MEASURED** or **INFERRED**.

## 1. THE LAYOUT I CHOSE

```
agents/tasks/LJ-1-141/LJ-1.141.md            the brief
agents/tasks/LJ-1-141/lj-1.141-report.md     the report
agents/tasks/LJ-1-141/ProbeLJ1141A.agda      the probe
```

| Path | What it holds | Count |
|---|---|---:|
| `agents/tasks/<CODE>/` | one LIVE task | **53** |
| `agents/tasks/archive/<CODE>/` | one task of the retired route | **494** |
| `agents/tasks/DD25/` | probes of a RULING, which is not a task | 55 probes |
| `agents/tasks/Unpaired/` | probes no report claims by name | 12 probes |

**`agents/briefs/` and `agents/reports/` are gone.** `agents/` now holds `README.md` and
`tasks/`, and nothing else.

**A file keeps the name it was born with.** Only the directory around it is new. A brief and a
report are frozen records and a renamed record breaks every citation that ever named it, so
`lj-1.141-report.md` is still `lj-1.141-report.md` and an old citation still resolves under
`find agents -name lj-1.141-report.md`. **This was a decision, not an omission**, and it is what
keeps 803 frozen citations one `find` away from their target instead of lost.

## 2. THE NAMING RULE, AND IT COVERS THE WHOLE CORPUS

> **The directory is the task code, in capitals, with `.` written `-`.**
> `LJ-1.142` is `LJ-1-142`. `L3.32-T126` is `L3-32-T126`. `t9-w7gate` is `T9-W7GATE`.

**It covers the corpus. MEASURED**, and the reason is that the corpus is narrower than it looks:
**every one of the 921 brief and report stems matches `[A-Za-z0-9.-]+` and every one starts with
a letter.** There is no `_` anywhere and no leading digit anywhere. So the rule's output is
always `[A-Z][A-Z0-9-]*`, which is the shape Agda accepts.

**The count the brief asked for is ZERO: no task's files failed to get one Agda-safe directory
name.** The two directories that are not tasks are named in section 5, fork 3.

### 2.1 I re-measured the Agda constraint at my own site (P-l)

`[LJ-1.141]` measured this in `/tmp`-free conditions and I did not take its word.

| Directory name | Result | Mechanism |
|---|---|---|
| `NAMETEST-L3-32-T126` | **exit 0** | capitals, digits and dashes |
| `NAMETEST-Geology-Legacy` | **exit 0** | mixed case, no numeric code |
| `nametest-lowercase` | **exit 0** | all lower case, the `archive` level |
| `NAMETEST-L3.32-DOT` | **exit 42** | `[ModuleNameDoesntMatchFileName]` |
| `NAMETEST-L3_32_UNDERSCORE` | **exit 42** | `[ParseError]` |

**The evidence is kept, not just claimed.** `agents/tasks/LJ-1-142/ProbeNameIndex.agda` imports
one probe per legal shape; the two negative controls are its sibling directories. Positive run:
**exit 0, 0.81 s, `GHCRTS=-M8g`, one process.**

**I refine `[LJ-1.141]`'s measurement on one point.** It reported a `.` as `[ParseError]`. That
is true only when the piece after the dot is a bare literal, as in `lj-1.141` where `141` is a
number. **When the piece after the dot parses as a name, the failure is
`[ModuleNameDoesntMatchFileName]` instead**, and Agda names a directory that does not exist:

```
LJ-1-142.NAMETEST-L3.32-DOT.ProbeNameNegDot
  ... should be defined in .../LJ-1-142/NAMETEST-L3/32-DOT/ProbeNameNegDot.agda
```

**Same verdict, different error. A checker that greps for `ParseError` would miss half the
cases.** MEASURED.

### 2.2 The rule is enforced by a machine, which it was not before

`scripts/tests/test_agents_tree.py` asserts that **every directory under `agents/tasks/` matches
`^[A-Za-z][A-Za-z0-9-]*$`**, and separately that the rule still REJECTS the two negative
controls. **A name test that has never rejected anything proves nothing**, so the test proves it
can fail. Nothing enforced this before: Agda resolves a module only when something imports it,
and nothing imports a closed task's probe, so a bad directory name would have landed green and
stayed green.

### 2.3 Pairing: a reversible rule plus a written table of 23

A whitelist of role suffixes (`-report`, `-review`, `-brief`) pairs most files. It leaves 23
pairs split, where a task's brief is `l3.32-t201.md` and its output is `l3.32-t201-decision.md`.
**I merged those 23 and wrote the table down**, because the brief forbids a mapping nobody can
reverse and a finite written table is reversible in a way a heuristic is not.

| Merged | Into | | Merged | Into |
|---|---|---|---|---|
| `B4E-FEASIBILITY-RECON` | `B4E` | | `L3-32-T259-CROSSING` | `L3-32-T259` |
| `L3-32-T201-DECISION` | `L3-32-T201` | | `L3-32-T260-BRIDGE` | `L3-32-T260` |
| `L3-32-T203-ROUTE` | `L3-32-T203` | | `L3-32-T263-FOF` | `L3-32-T263` |
| `L3-32-T210-CAMPAIGN` | `L3-32-T210` | | `LJ-0-2-SUFFICIENCY` | `LJ-0-2` |
| `L3-32-T213-MATH` | `L3-32-T213` | | `LJ-0-3-RETROSPECTIVE` | `LJ-0-3` |
| `L3-32-T218-WALL` | `L3-32-T218` | | `LJ-0-4-COMPRESSION` | `LJ-0-4` |
| `L3-32-T219-SECONDS` | `L3-32-T219` | | `LJ-1-1-RECON` | `LJ-1-1` |
| `L3-32-T223-PLAN` | `L3-32-T223` | | `LJ-1-10-REPRICE` | `LJ-1-10` |
| `L3-32-T230-BLOCKA` | `L3-32-T230` | | `LJ-1-127-AGENTS-DIFF` | `LJ-1-127` |
| `L3-32-T250-MATH` | `L3-32-T250` | | `LJ-1-2-GATE` | `LJ-1-2` |
| `L3-32-T255-SECONDS` | `L3-32-T255` | | `R3A-WALLS` | `R3A` |
| `L3-32-T257-ROUTES` | `L3-32-T257` | | | |

**Two of the 23 are a judgment and I mark them: INFERRED.** `B4E-FEASIBILITY-RECON` into `B4E`
and `R3A-WALLS` into `R3A` merge a follow-up document into the task whose code it carries. The
other 21 pair a brief with the output that brief ordered, which is not a judgment.

### 2.4 The 35 `T*` directories `[LJ-1.141]` could not place

`[LJ-1.141]` derived a probe's directory from the PROBE's name, so `ProbeT126.agda` became
`T126`. **The task is `L3.32-T126` and its brief and report were in a different tree.**
MEASURED: each of the 35 bare-`T` names resolves to **exactly one** `l3.32-tNNN` task, with no
ambiguity, so all 35 are now merged into their real task directory.

## 3. THE COUNTS

| | |
|---|---:|
| Task directories | **547** (53 live, 494 archived) |
| Non-task buckets kept | 2 (`DD25`, `Unpaired`) |
| Files moved, tracked, as git renames | **1,178** |
| Briefs and reports now in task directories | **921** |
| Probes | **264** (258 inherited, 6 mine) |
| Directories holding BOTH a brief and a report | **338** |
| Directories holding a probe | **117** |
| Live citation tokens rewritten | **358**, across **36 files** |
| Of those, brace families expanded and verified | **1** |
| Rewritten paths that resolve on disk | **320**, **0 dangling** |
| Files under `agents/` before and after | **1,187 → 1,187** |

**Nothing was lost. MEASURED:** `git status` reports 1,178 renames, 0 deletions, and the file
count under `agents/` is unchanged.

### 3.1 The citation rewrite, and the recall bug bit me in the dry run

**I counted before moving anything: 376 live citation tokens**, in this shape:

| Shape | Count |
|---|---:|
| `agents/reports/archive/<file>.md` | **270** |
| `agents/reports/<TASKDIR>/<probe>.agda` | 32 |
| bare `agents/reports/` or `<TASK>` placeholder | 30 |
| `agents/reports/<file>.md` | 20 |
| bare `agents/briefs/` | 11 |
| `agents/briefs/<file>.md` | 9 |

**The rewriter resolves against the TREE, not against a pattern.** It takes each token's
basename and looks up where that file now is. MEASURED: **zero duplicate basenames** exist under
`agents/tasks/`, so the lookup is unambiguous.

**`[LJ-1.133]`'s brace bug bit me, and the dry run is where it bit.** My first tokenizer excluded
`,`, so `agents/reports/DD25/ProbeDD25F41{A,B,C,D}.agda` at `dev/LESSONS.md` was captured as
`...ProbeDD25F41{A` and reported UNRESOLVED. **A dry run that prints what it cannot resolve is
what turned a silent dangle into a visible one.** The fixed tokenizer admits a `{...}` group,
expands the family, resolves all four members, and requires them to share one directory. They
do.

**The range form `A..F` is supported and MEASURED to be unused today**: zero live range citations
exist.

## 4. THE FOURTEEN CONSUMERS

The brief named thirteen. **`scripts/check-sources-read.py` is the fourteenth**, and it reads
`ROOT / "agents" / "briefs"` at line 45. It is not in `make check`; `dev/ORCHESTRATION.md:460`
tells the orchestrator to run it by hand after every dispatch. **It would have failed silently
on the next audit.**

| # | Consumer | Result |
|---|---|---|
| 1 | `check-build-manifest.py --check` | **exit 0**, every `_build/` file declares a lifecycle |
| 2 | `check-dispatch-policy.py` | **exit 0**, `override` in force, **442 briefs read**, 31 notes |
| 3 | `check-dev-docs.py` | **exit 0**, 6 subchecks |
| 4 | `check-rule-ids.py` | **exit 0**, 45 files, 141 lessons, 66 decisions |
| 5 | `check-probes.py --check` | **exit 0**, 1,594 tracked files, no probe outside `agents/tasks/` |
| 6 | `check-unbound-hyp.py` | **exit 0**, its two cited probe paths follow the move |
| 7 | `check-task-index.py` | **exit 0**, 445 cited codes, 457 rows |
| 8 | `deletion-test.py` | **exit 0**, its one cited report path follows the move |
| 9 | `dd25-record.py` | **exit 0**, its one cited report path follows the move |
| 10 | `ledger.py --check` | **exit 0**, standing **28,617 over 85 masters, unchanged** |
| 11 | `.gitignore` | **exit 0** through the live gate; its comment names the new home |
| 12 | `Makefile` | **exit 0**; the new suite is wired into `make test` |
| 13 | `bedrock.agda-lib` | **exit 0**; `include: src agents/tasks`, re-verified with Agda |
| 14 | **`check-sources-read.py`** (NOT in the brief) | **exit 0** on `LJ-1.141` |

**C-40, and the census is the point.** `check-dispatch-policy.py` reads **442 briefs**, not zero.
I added an explicit guard: if the brief list is ever empty the checker now FAILS with
`the census is ZERO`, instead of passing by reading nothing.

**The staged gate is reading a real set. MEASURED:** 1,178 staged renames, of which **258 are
probes**, and `check-probes.py --staged` is exit 0 over them.

Also green, and none of them is in the brief's list: `reuse lint` (compliant, `agents/**` is CC
through the existing carve-out, **no `REUSE.toml` change was needed**), `check-tree.py --check`
(87 masters), `lint-prose.py --check` over the whole tree, and **all 11 suites in
`scripts/tests/`**, including the new one.

### 4.1 The merge deleted a signal five checkers were reading

**This is the finding that cost the most and it is not in the brief.** Until today a brief was a
file in `agents/briefs/` and a report was a file in `agents/reports/`. **The DIRECTORY carried
the distinction.** Five checkers each wrote `ROOT / "agents" / "briefs"` and each was right.
**The merge deleted that signal**, and a `Path`-style construction is invisible to any
string-level path rewriter, so none of the five would have been touched by the citation pass.

`scripts/agents_tree.py` is the replacement, written once and read by all five (the DD4
instinct, applied to tooling). **It offers two predicates because one is not safe for every
caller:**

| Predicate | Basis | MEASURED against the 920 files, while the source directory was still ground truth |
|---|---|---|
| `briefs()` | content | **415 of 415 found, 0 missed, 0 of 505 reports misread** |
| `candidate_briefs()` | name | 415 of 415 found, **27 archived reports misread** |

The content signals are strong and I measured each: **`ARCHIVE USED` appears in 168 reports and
in NO brief**; a `STATUS:` line in the first twelve lines appears in **214 reports and in NO
brief**; `SCOPE (read)` appears in **332 briefs and in NO report**.

**A checker hunting a MISSING `tier:` line must take the NAME-based set**, because the
content-based one finds a brief partly BY its `tier:` line and would never see the defect. That
is a trap I walked into and backed out of: my first version had `check-dispatch-policy.py`
calling `briefs()`. **It pays for the wider set by never FAILING an archived record**, and all
27 misreadings are under `archive/`.

## 5. THE FORKS, WITH MY RECOMMENDATION

### Fork 1: rename the root. **I renamed it, and the two forks are coupled**

**RECOMMENDED AND DONE: `agents/reports/` → `agents/tasks/`.**

The brief prices this as "renaming the root changes `include:` and every citation". **MEASURED,
that is true but it is not the marginal cost, because forks 1 and 2 are coupled.** Under fork 2
below, the 270 archive citations are being rewritten anyway. Once they move, the root rename
rides along in the same pass, on the same tokenizer, with the same verification.

**The decisive argument is timing, not taste. The rename is cheapest exactly now.** Deferring it
means rewriting the same citations a second time and making the frozen corpus stale twice.

Against keeping the name: a directory called `reports` that holds briefs is read by every future
agent, and `dev/ORCHESTRATION.md`'s standing clause points at it in every brief. **A wrong name
is paid forever; the citations are paid once, mechanically, with every path verified against
disk.**

### Fork 2: the 452 archived reports. **RECOMMENDED AND DONE: they get directories too**

**A flat archive is not merely less consistent. It is structurally incoherent with the ruling,
and that is MEASURED, not an opinion.**

The probes decide it. 117 of the 119 probe directories map to a task, and **a large share of
them belong to RETIRED tasks**: all 35 bare-`T` directories are `l3.32-t*`, and `LJ-1-15`
through `LJ-1-89` are archived. Under a flat archive those probe directories would have stayed
at the top level while their brief and report sat in `archive/`, **splitting the task across two
places, which is the exact defect the ruling removes.** There is no flat arrangement that keeps
a retired task's three halves together.

The cost is 494 directory entries and 270 rewritten citations. **The citations were the thing to
fear and they are verified: 320 resolve, 0 dangle.**

### Fork 3: unpaired files. **Counted, and two buckets are named**

| | Count |
|---|---:|
| Directories with a brief AND a report | **338** |
| Directories with a brief and no report | **78** |
| Directories with a report and no brief | **104** |

**These are not defects and they need no decision.** A brief with no report is a dispatch whose
report never landed; a report with no brief is a dispatch briefed before briefs were kept. A
directory with one file in it is fine, as the brief says.

**Two things could NOT be assigned to a task, and I name them rather than invent a mapping:**

1. **`agents/tasks/DD25/`, 55 probes.** `DD25` is a RULING, not a task. No brief and no report
   carries that code. `dev/LESSONS.md` cites six of these probes as the provenance of live
   rules, so the directory is load-bearing and it keeps its name.
2. **`agents/tasks/Unpaired/`, 12 probes.** No report claims them by name.

**I could have assigned 9 of the 12 and I deliberately did not.** `archive/probes/README.md`
records the strongest citation each one carried, and 9 name a single report:
`CutProbe.agda ← cut-probe-report.md:56`, `ProbeBelowLim.agda ← l3.32-t127-report.md:87`, and
so on. **A citation records who CITED the file, not who WROTE it**, and the remaining 3 point at
`dev/LESSONS.md` and `dev/ledger.toml`, which are not tasks at all. **Assigning on that evidence
is exactly the mapping nobody can reverse.** The evidence is in the tombstone if the owner wants
it settled; it is a 12-file follow-up.

### Fork 4: the non-report data files. **Left where they are**

`agents/tasks/archive/tmp-cond-dd3aa13.lagda.md`, 392 KB, is a copy of a chapter, not a record
of a dispatch. **It stays flat, outside every task directory**, and `agents_tree.documents()`
excludes `.lagda.md` explicitly so no checker reads it as a report. The 20 files the owner left
in `_build` at `[LJ-1.130]` are untouched; **MEASURED: `check-build-manifest.py --check` is exit
0 and every file in `_build/` still declares a lifecycle.**

**MEASURED: `agents/` holds exactly two file extensions, `.md` and `.agda`.** There was no
fourth species to discover.

## 6. WHAT A READER GAINS AND WHAT THEY LOSE

**GAINS.** One directory answers "what happened in `[L3.32-T126]`": the brief that ordered it,
the report that returned it, and the probe that measured it, in three files instead of three
trees. 338 directories deliver all of that today. A new agent writes its probe into the
directory it is already reading its brief from, so the two halves of a task cannot drift apart.

**LOSES, and this is the honest half.**

1. **803 frozen citations in briefs, reports and `archive/` now name a path that does not
   exist.** MEASURED. They are frozen records and nothing rewrites them (`[LJ-1.130]`).
   **The mitigation is real but partial: no file was renamed, so `find agents -name <basename>`
   still finds every one of them.** That is why I did not rename files.
2. **`archive/probes/README.md`, the tombstone `[LJ-1.141]` wrote this afternoon, is now one hop
   short.** Its 257-row map points at `agents/reports/<TASK>/`. **It is in `archive/`, which the
   brief puts outside my write scope**, so I did not touch it. **OWED to the orchestrator:** one
   sentence at its head saying the root is now `agents/tasks/` and the retired route's probes
   moved under `archive/`.
3. **A reader can no longer tell a brief from a report by its directory.** Section 4.1 is the
   replacement and it is measured, but a human skimming a directory listing now reads filenames
   instead of paths.

## 7. WHAT I WROTE INTO THE NEW LAYOUT, SINCE I AM THE FIRST

The brief asks what it felt like. **It removed a step rather than adding one.** My brief was
already at `agents/tasks/LJ-1-142/LJ-1.142.md`, so the skeleton report went beside it with no
decision about where, and the five naming probes went into the same directory without my having
to invent a home or a name for them. **I never had to ask where a file goes**, which is the
whole benefit and it is small per task and paid every task.

**One thing was awkward and I fixed it rather than report it as fine.** My naming probes needed
directories named after the SHAPES under test, and my first version used the real shapes:
`T126`, `archive`, `Unpaired`, `GEOLOGY-LEGACY`. That put duplicate task names inside a task
directory, so `find agents -name T126` returned two hits. **I renamed them to `NAMETEST-*` and
re-ran the measurement** rather than leave a permanent confusion in the tree that a reader would
have to learn.

## 8. EVERY NEGATIVE, MARKED

- **MEASURED.** `agda agents/tasks/LJ-1-142/ProbeNameIndex.agda` exits 0 in 0.81 s under
  `GHCRTS=-M8g`, one process, resolving three legal directory-name shapes.
- **MEASURED.** A `.` in a directory name fails as `[ModuleNameDoesntMatchFileName]` when the
  piece after it parses as a name, and as `[ParseError]` when it is a bare literal. `[LJ-1.141]`
  reported only the second. Both are exit 42.
- **MEASURED.** A `_` fails as `[ParseError]`: "in the name `NAMETEST-L3_32_UNDERSCORE`, the part
  32 is not valid because it is a literal".
- **MEASURED.** After the root rename, `agda agents/tasks/LJ-1-141/ProbeLJ1141A.agda` exits 0 in
  1.08 s. **The second include root still resolves the tower from `src/` under its new name.**
- **MEASURED.** Every one of the 921 brief and report stems matches `[A-Za-z0-9.-]+` and starts
  with a letter. No `_`, no leading digit. **That is why the naming rule covers the corpus, and
  the count of files that could not be named is ZERO.**
- **MEASURED.** Each of the 35 bare-`T` probe directories resolves to exactly one `l3.32-tNNN`
  task. No ambiguity.
- **MEASURED.** Zero duplicate basenames exist under `agents/tasks/`, so the citation resolver is
  unambiguous.
- **MEASURED.** 358 citation tokens rewritten in 36 live files; 320 resolve on disk; **0
  dangle**. The 12 that do not resolve are synthetic gate fixtures in `check-probes.py` and
  `test_probe_gate.py` and are supposed not to exist.
- **MEASURED.** The brace family `ProbeDD25F41{A,B,C,D}.agda` was captured wrong by my first
  tokenizer and appeared in the DRY RUN's unresolved list. All four members share one directory.
- **MEASURED.** 1,178 tracked renames, 0 deletions, file count under `agents/` unchanged at
  1,187.
- **MEASURED.** `scripts/check-sources-read.py:45` reads `agents/briefs/` and is a consumer the
  brief did not list. Fourteen, not thirteen.
- **MEASURED.** The brief predicate: content-based is 415/415 with 0 reports misread; name-based
  is 415/415 with 27 archived reports misread. `ARCHIVE USED` and a leading `STATUS:` appear in
  no brief; `SCOPE (read)` appears in no report.
- **MEASURED.** `check-dispatch-policy.py` reads 442 briefs, not 0, and now fails explicitly if
  that list is ever empty.
- **MEASURED.** `check-probes.py --staged` runs over 1,178 staged renames of which 258 are
  probes, and is exit 0.
- **MEASURED.** `ledger.py --check` reports standing 28,617 over 85 masters, unchanged. The scan
  is scoped to `src/**.lagda.md`, so `agents/` is outside it by construction.
- **MEASURED.** `reuse lint` is compliant with no `REUSE.toml` change. `agents/**` is CC through
  the existing carve-out and the rename does not leave it.
- **MEASURED.** All 11 suites in `scripts/tests/` pass, including `test_ratio_baseline.py`, which
  was red during `[LJ-1.141]`'s run. I did not fix it and I do not claim it: a sibling's work on
  `src/L/Condensation.lagda.md` landed between the two runs.
- **MEASURED.** `check-rule-ids.py --briefs` exits 1 with **2** dangling references. **NOT
  MINE.** I crossed every defect against the pre-move directory of its file: 2 are in files that
  were briefs at HEAD and were already red; the other 32 my first, wider predicate had newly
  pulled in from frozen archived reports, and the final predicate excludes them. **`make check`
  runs this checker WITHOUT `--briefs`**, and that run is exit 0.
- **MEASURED.** `dev/PLAN.md:610` and `:621` still write `agents/reports`. **Both are section 11
  verdict cells recording what those dispatches found on their day.** I read them as frozen rows
  and left them, following `[LJ-1.141]`, which left `dev/PLAN.md:513` for the same reason. PLAN
  is the orchestrator's. **OWED.**
- **INFERRED.** That merging `B4E-FEASIBILITY-RECON` into `B4E` and `R3A-WALLS` into `R3A` is
  right. Both share a task code with the target and read as follow-ups, but **I did not open
  them to confirm one dispatch produced both.** The other 21 merges pair a brief with the output
  it ordered and are not inferences.
- **INFERRED.** That the 78 brief-only and 104 report-only directories are all genuine
  singletons rather than pairs my rule failed to join. The 23-row table is the set my near-miss
  scan found at a `-` boundary; **a pair whose two names share no prefix would be invisible to
  it** and I have no measurement that says none exists.
- **INFERRED.** That no future module name collides between `src/` and `agents/tasks/`. Today's
  risk is zero, MEASURED by `[LJ-1.141]`, and the rename does not change it. It is a convention,
  not a gate.
- **INFERRED.** That `make check`'s wall time does not move. **I did not measure it**; the brief
  forbids running it. The mechanism is one renamed directory in the module search path.
- **INFERRED.** That nobody needs the 12 `Unpaired` probes assigned. If somebody does, the
  tombstone's citation column is the evidence and 9 of 12 are settleable from it.

## 9. WHAT I CHANGED, BY FILE

**New:** `scripts/agents_tree.py` (the shared layout module),
`scripts/tests/test_agents_tree.py` (32 checks), this report, and six probes under
`agents/tasks/LJ-1-142/`.

**Moved:** 1,178 files, as git renames.

**Modified for citations only:** `dev/LESSONS.md`, `dev/ledger.toml`, `dev/PLAN.md`,
`dev/ORCHESTRATION.md`, `dev/ARCHIVE.md`, `dev/JOURNAL.md`, `dev/build-manifest.toml`,
`dev/measurements/README.md`, six files under `dev/memos/`, four under `dev/literature/`,
`.gitignore`, `Makefile`.

**Modified for behaviour:** `bedrock.agda-lib` (the include root),
`scripts/check-dispatch-policy.py`, `scripts/check-task-index.py`, `scripts/check-rule-ids.py`,
`scripts/check-sources-read.py`, `scripts/check-dev-docs.py` (all five now read
`agents_tree.py`), `scripts/check-probes.py`, `scripts/check-build-manifest.py`,
`scripts/check-unbound-hyp.py`, `scripts/ledger.py`, `scripts/deletion-test.py`,
`scripts/dd25-record.py`, `scripts/tests/test_probe_gate.py`, `scripts/tests/test_task_index.py`,
`scripts/README.md`, `agents/README.md`, `Makefile` (wires the new suite into `make test`).

**NOT touched, and deliberately:** `AGENTS.md` (section 10), `archive/**` (outside my write
scope; the tombstone is section 6), `src/ProbeLJ1134A.agda`, `src/ProbeLJ1136A.agda`,
`src/ProbeLJ1136B.agda`, `dev/PLAN.md`'s section 11 verdict cells.

**I did not delete one file. I did not commit. I did not push. I ran Agda five times, one
process at a time, never above `-M8g`. I did not run `make check`.**

## 10. THE `AGENTS.md` LINE I PROPOSE, FOR THE OWNER. DD19

**I did not edit `AGENTS.md`.** I read it fresh today, as the brief requires.

**`AGENTS.md:105` is now false.** It reads:

> **Agent reports and briefs.** Every dispatch writes one of each. Live reports in
> `agents/reports/`, older in `agents/reports/archive/`, every brief in `agents/briefs/`. All
> tracked, all CC, all exempt from the prose linter because a record is never rewritten

Proposed replacement, which is **7 words shorter**, so the word cap gains:

> **Agent tasks: one directory each.** Every dispatch writes a brief, a report and its probes,
> and all three live in `agents/tasks/<CODE>/`, or `agents/tasks/archive/<CODE>/` for the
> retired route. `<CODE>` is the task code with `.` written `-`, because that directory is an
> Agda module name component. All tracked, all CC, all exempt from the prose linter because a
> record is never rewritten

**This needs the owner's ruling and a dated `AGENTS-diff-approved:` trailer** (DD19,
`scripts/check-agents-guard.py`). MEASURED: `check-dev-docs.py` is exit 0 today, and I did not
verify the post-edit word count because I did not make the edit.

## 11. LITERATURE (DD18)

**Nothing in the literature governs a directory layout.**

## 12. ARCHIVE USED

- **`agents/tasks/LJ-1-141/lj-1.141-report.md`**, read WHOLE. Took: the four naming measurements
  at `:93-106`, which I re-measured at my own site per P-l and which reproduced with the one
  refinement in section 2.1; the frozen-record ruling at `:176-180`, which decided that I move
  files and never rename them; the `Unpaired`/`DD25` grouping at `:81-88`, whose two unassignable
  buckets I kept and named; the tombstone it wrote at `:303`, which section 6 records as one hop
  short; and the `T126`-shaped directories at `:104-106`, whose task I could place and it could
  not.
- **`agents/tasks/LJ-1-133/lj-1.133-report.md`**, read WHOLE. Took: **the two recall bugs at
  `:170-186` and `:462-476`**, the brace `{A,B,C,D}` and the range `A..F`. **The brace one bit my
  dry run**, exactly as predicted, on the same `dev/LESSONS.md` citation; the frozen-record
  ruling at `:105-110`; and the "an honest undecided beats a wrong deletion" reasoning at
  `:268-272`, which is why `Unpaired` still has 12 files in it.
- **`agents/tasks/LJ-1-130/lj-1.130-report.md`**, via its citation trail: the 283-citation
  rewrite is the precedent that a several-hundred-citation pass is routine here when every path
  is verified against disk.
- **`REUSE.toml`**, read WHOLE. `agents/**` is CC through the carve-out at `:31-35`, which is a
  path prefix that the rename does not leave, so **no entry was needed. MEASURED:** `reuse lint`
  compliant.
- **`archive/probes/README.md`**, read. Took its 12 `Unpaired` rows with their strongest-citation
  column, which is the evidence in fork 3 that I decided NOT to act on.
- **`dev/ARCHIVE.md`** and **`archive/README.md`**, read. Both index retired MODULES and neither
  has a column that fits a directory layout, which `[LJ-1.132]`, `[LJ-1.133]` and `[LJ-1.141]`
  each found. **I added no row**, following that precedent.
- `bedrock.agda-lib`, `dev/ORCHESTRATION.md:160-215,355-365`, `scripts/check-probes.py` (whole),
  `scripts/check-dispatch-policy.py:160-258`, `scripts/check-dev-docs.py:350-375`,
  `scripts/check-task-index.py`, `scripts/check-rule-ids.py:255-275`,
  `scripts/check-sources-read.py`, `Makefile:160-180`, `agents/README.md` (whole).

## 13. DD4

**Nothing in this task touched a proof, so DD4 had no line to share.** The task was a layout and
its tooling.

**Where the DD4 instinct applied is section 4.1, and it applied because the alternative was
visible.** Five checkers were about to need the same new knowledge: where the task tree is, and
which file in it is a brief. **The fixed way is five copies of a path and five copies of a
predicate, which is exactly the "write it fixed" failure in tooling form**, and it would have
drifted the first time the predicate needed a correction. `scripts/agents_tree.py` is the
generic form: one module, five readers, and the measured limit of the predicate stated once
where all five see it.
