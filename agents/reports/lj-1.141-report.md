# LJ-1.141 report: a probe lives beside its report, tracked, never deleted

STATUS: **DONE.** The rehome works in this tree, MEASURED. 258 probes sit in 118
per-task directories. The lifecycle is retired and archived. The document census
is complete. **Nothing committed. Nothing pushed. Nothing deleted.**

Every negative below is marked **MEASURED** or **INFERRED**.

## 1. IT WORKS IN THIS TREE. MEASURED

**The layout the owner ruled runs today.**

```
$ agda agents/reports/LJ-1-141/ProbeLJ1141A.agda
Checking LJ-1-141.ProbeLJ1141A (/Users/alsg/Agentic/Bedrock/agents/reports/LJ-1-141/ProbeLJ1141A.agda).
real 1.22
EXIT=0
```

**Exit 0, 1.22 s warm, `GHCRTS=-M8g`, one process, load average 5.0.**
`bedrock.agda-lib` now reads `include: src agents/reports`.

That probe sits beside `agents/reports/lj-1.141-report.md`, this file. It is
the worked example of the new rule and it is tracked.

Five things are MEASURED here that `[LJ-1.138]` could not measure in `/tmp`
(P-l):

1. **A path with a separator works in `include:`.** `[LJ-1.138]` used
   single-component names (`mastersdir probesdir`). `agents/reports` carries a
   `/`; Agda splits the line on whitespace only.
2. **A module under the second root imports the tower under the first.**
   `ProbeLJ1141A` opens `Base.Prelude` and `L.Stage`, which pulls
   `Base.Truth`, `Base.Classical`, `FOL.ZFStructure`, `V.Hierarchy`,
   `L.Constructible` and `L.Ordinal.Linear`. All resolved from `src/`.
3. **A per-task subdirectory becomes the module QUALIFIER.** The file declares
   `module LJ-1-141.ProbeLJ1141A`. That is the whole cost for a NEW probe: one
   line, written once, by the agent who writes the probe.
4. **The interface does NOT land beside the source.** MEASURED:
   `_build/2.8.0/agda/agents/reports/LJ-1-141/ProbeLJ1141A.agdai`.
   `agents/reports/` gains no `.agdai`.
5. **`_build/2.8.0/agda/` now holds two subtrees, `src` and `agents`.**
   `dev/build-manifest.toml:106` classes `2.8.0/**` as `toolchain`, so the new
   subtree needs no entry.

## 2. THE ROT QUESTION: ANSWERED BY RULING, NOT BY MEASUREMENT

**The owner ruled option 1 on 2026-08-13: a probe is TEXT after its task
closes.** Nothing typechecks it. No `make check` cost, no `make probes-check`,
no CI. **My DD8 gate is answered by ruling, not by measurement**, and I present
no price for options 2 and 3 because nobody asked for one.

**What the ruling does NOT remove, and it is why the include root exists at
all.** A probe must typecheck WHILE its task runs. The second include root
buys **write-and-run-in-place**: the agent writes the probe in its final home,
runs it there, and the file never moves, so no citation into a probe is ever
rewritten a second time.

**One consequence, stated once.** A probe's claim is true of the tree at its
date and is never re-verified. That is already true of every report in
`agents/`, so it changes nothing about how evidence works here.

**One measurement I had already taken before the ruling arrived, kept because
it shows the ruling costs nothing.** A random sample of 10 of the 257 archived
probes, seed 1141, typechecked one process at a time under `GHCRTS=-M8g`:
**4 GREEN, 6 RED**, five of the six with `[FileNotFound]` on a module that no
longer exists. **The corpus had already rotted.** A rule that stopped
typechecking them was not giving up a green corpus; there was none.

## 3. THE LAYOUT: per-task directories under `agents/reports/`

**RULED by the owner: a task's probes go in a directory of their own.**

```
agents/reports/lj-1.141-report.md          the report
agents/reports/LJ-1-141/ProbeLJ1141A.agda  its probes
```

**258 probes now sit in 118 directories.** MEASURED, and the shape is:

| Directory | Probes | What it is |
|---|---:|---|
| `LJ-1-74` | 10 | the largest single task |
| `LJ-1-32` | 8 | |
| `T258` | 7 | the retired `T` series resolves the same way |
| `DD25` | 55 | a DECISION code, not a task |
| `Unpaired` | 12 | no report carries their code |
| 113 others | 1 to 6 each | |

### 3.1 The directory NAME is constrained by Agda, and that is measured

**A directory under an include root becomes a module name component, so it
must parse as an Agda name.** MEASURED 2026-08-13, all four in Agda 2.8.0:

| Directory | Result |
|---|---|
| **`LJ-1-141`** | **OK.** A dash does not split a name |
| `lj-1.141` | `[ParseError]` — `.` splits the qualifier, `141` is then a literal |
| `LJ-1_141` | `[ParseError]` — `_` splits a mixfix name, `141` is then a literal |
| `LJ_1_141` | `[ParseError]` — same |

**So the directory cannot carry the report's own name.** `LJ-1-141` is the
closest legal form to the code `LJ-1.141`, and one substitution reads it: the
dot becomes a dash. It also kills an ambiguity that cost `[LJ-1.138]` a whole
regex: `ProbeLJ1134A` parses to `LJ-1.134`, `LJ-11.34` and `LJ-113.4`, while
`LJ-1-134` names exactly one task.

### 3.2 A task with ONE probe still gets a directory

**I agree with the simple rule and I recommend it.** 113 of the 118
directories hold fewer than 7 files and most hold one. The alternative is a
rule with a threshold, and a threshold means an agent asks 「is this the second
one?」 before writing a file. **The cost of the simple rule is 118 directory
entries. The cost of the threshold rule is a decision per probe.**

### 3.3 THE 257 HISTORICAL PROBES ARE MOVED, NOT EDITED, and here is why

**Their module lines still name the flat form.** `agents/reports/LJ-1-99/ProbeLJ199A.agda`
declares `module ProbeLJ199A`, not `module LJ-1-99.ProbeLJ199A`. **MEASURED:
Agda refuses that with `[ModuleNameDoesntMatchFileName]`.**

**I did not edit them, and the reason is measured three ways:**

1. **Nothing typechecks them** (the owner's ruling). They are text.
2. **They were already RED.** 6 of 10 sampled fail against today's tree, five
   with `[FileNotFound]`. Repairing the module line would not make one green.
3. **The edit is not one line per file.** MEASURED: **45 of the 258 probes
   import another probe by its flat module name** (`open import ProbeLJ199A
   {ℓ} lem using ( module ChainZ )`), and several of those imports cross task
   boundaries. A correct rename is 258 module lines PLUS 45 import statements
   that must each learn another task's directory.

**And `agents/README.md` says this tree holds frozen records that nobody
edits.** A mass edit of 258 evidence files, to make green a corpus that is not
green, against a rule that says nothing checks them, buys nothing.

**INFERRED: nobody wants to re-run a historical probe.** If somebody does, the
error names the expected module name and the repair is the one line Agda
prints. **I am recording that as a known cost of the per-task layout**, and it
is the only cost the flat layout would not have had.

### 3.4 The one latent trap in this tree

**MEASURED.** `agents/reports/archive/tmp-cond-dd3aa13.lagda.md` exists, and it
is an Agda-readable literate file under the new include root. Its module path
would be `archive.tmp-cond-dd3aa13`. **Nothing breaks today**, because Agda
resolves a module only when something imports it. **INFERRED:** that no future
name collides.

## 4. THE CITATION COUNT, BEFORE THE MOVE

**Counted before anything moved, as instructed.**

| Where | Occurrences of `archive/probes/` | Treatment |
|---|---:|---|
| `dev/LESSONS.md` | 22 | **rewritten** |
| `dev/ledger.toml` | 3 | **rewritten** |
| `dev/memos/L3.30-rud-route.md` | 1 | **rewritten** |
| `dev/memos/L3.32-below-lim-design.md` | 1 | **rewritten** |
| `agents/reports/*.md`, `agents/briefs/*.md` | 65 | **left, frozen records** |
| `scripts/*` | 15 | rewritten or retired with their code |

**27 citations rewritten in live `dev/` documents. Zero dangle.** MEASURED by
resolving every rewritten path against the file on disk: **30 resolve** (27
occurrences, one of which is the four-member brace family), **0 dangling**.

**`[LJ-1.133]`'s two recall bugs did not bite, and the reason is structural
rather than lucky.** The brace form `agents/reports/DD25/ProbeDD25F41{A,B,C,D}.agda`
at `dev/LESSONS.md` and the range form `A..F` both survive a PREFIX rewrite
untouched, because **every member moved to the same directory**. MEASURED: the
`Unpaired` and `DD25` groups are whole; no family is split across two
directories. A rewriter still has to expand a brace to VERIFY resolution, and
mine does.

**The 216 frozen briefs writing `src/Probe` are unchanged**, and so are the
251 reports. `[LJ-1.130]` rules that a brief and a report are frozen records,
corrected in the next one and never rewritten. **What it costs a reader:** a
path in a brief from before 2026-08-13 does not resolve, and
`archive/probes/README.md` is the tombstone that maps the old path to the new
one.

**AND IT COST SOMETHING DURING MY OWN RUN. MEASURED.** A sibling wrote
`src/ProbeLJ1136A.agda` at 15:06 today, while I was moving 257 probes out of
`src/`. **That is `[LJ-1.138]`'s decider happening live**: an agent under a
frozen brief writes to `src/`, and no ruling reaches it. **The gate still
refuses to COMMIT it, which is the guarantee that matters**, and the file is a
sibling's live work so I did not touch it. **The rule becomes structural only
when the briefs an agent reads name the new place.** New briefs do; old ones
are records.

## 5. THE GATE HOLE I FOUND, and it was live

**MEASURED, and it is the one defect this task found by itself.**
`scripts/check-probes.py`'s `--staged` mode read
`git diff --cached --name-only --diff-filter=ACM`. **A staged RENAME is `R`,
and `ACM` does not include it.**

```
257 probe renames staged
  --diff-filter=ACM   reports   0
  --diff-filter=ACMR  reports 254   (the 254 whose basename starts with Probe)
```

**Why it matters now and did not before.** While probes were untracked, a probe
had nothing to be renamed FROM. A probe is tracked now, so
`git mv agents/reports/LJ-1-99/ProbeLJ199A.agda src/ProbeLJ199A.agda` would
have passed the pre-commit hook. **The filter now carries `R`**, and the fix is
pinned end to end in `scripts/tests/test_probe_gate.py`.

**Verified in both directions, on a THROWAWAY index so the real one is never
touched:**

| Test | Result |
|---|---|
| a probe staged under `src/` | **exit 1, REFUSED** |
| the same probe staged in `agents/reports/` | **exit 0, accepted** |
| an `.agdai` staged in `agents/reports/` | **exit 1, REFUSED** |
| a probe `git mv`-ed from its home INTO `src/` | **exit 1, REFUSED** |

**`[LJ-1.133]` did this by writing a real file into `src/` and deleting it
afterwards.** I used `GIT_INDEX_FILE` against a copy of the index instead, so
no file entered `src/` and the real index never changed. That also honours the
new ruling, which is that nothing is deleted.

## 6. WHAT SURVIVES OF `[LJ-1.138]`'s SWEEP, and what retires

**RETIRED, by the owner's ruling.** `--gate`, `--stale`, `--sweep`, `--index`,
`--archive`, `--delete`, `--floor-hours`, the live-task trigger read off
`dev/PLAN.md`, the four verdicts, the one-hop citation test, the shorthand
recall cure and the 24-hour deletion floor. `make probes-sweep` is gone and so
is the `--gate` line in `make probes`.

**ARCHIVED, never deleted.** `archive/tooling/check-probes-lifecycle.py` (672
lines) and `archive/tooling/test_probe_lifecycle.py` (260 lines), frozen at the
moment of retirement, with an entry in `archive/tooling/README.md`.

**SURVIVING, and not open.** `--check` and `--staged`. `src/` is refused
absolutely; the ONE exemption is `agents/reports/`.

**No dead code path is left.** Every retired flag now exits 2 with a usage
message, and `scripts/tests/test_probe_gate.py` pins that none of them prints a
success line.

## 7. SIZE

**MEASURED before the move: `archive/probes/` was 8,664 KB over 257 files,
159,949 lines**, mean 33.7 KB. **Ten files carry 3.9 MB of that**, the
`ProbeLJ173A` / `ProbeLJ174*` / `ProbeLJ175A` family at about 390 KB each.

The corpus is now tracked in `agents/reports/`. It was already tracked in
`archive/probes/` before I started, so **this task adds no bytes to the
repository**; it moves them.

## 8. THE DOCUMENT CENSUS

### 8.1 How I searched, and my first two searches were NOT a census

**Pass 1** listed every live file containing the word `probe`: **47 files.** Too
coarse to act on.

**Pass 2** was a proximity regex: `probe` within 120 characters of
`never committed|thrown away|throwaway|swept|sweep|delete|working tree|...`.
**It found 24 lines and it MISSED three of the coordinator's eight**, including
`AGENTS.md:135` and `dev/PLAN.md:172`. **The reason is the shape of the
sentences:** 「Build the smallest decisive miniature, report GO or NO-GO with a
price, throw it away」 puts the word `probe` in the PREVIOUS sentence, and
「Nobody commits a probe」 puts it after the verb. **A proximity regex over prose
that varies its subject is not a census, and this is the measurement that says
so.**

**Pass 3 is the census.** Every line containing `probe`, case-insensitive, in
every LIVE document: `AGENTS.md`, `CLAUDE.md`, `README.md`, `Makefile`,
`.gitignore`, `.pre-commit-config.yaml`, `dev/*.md`, `dev/*.toml`,
`dev/memos/*.md`, `scripts/*.py`, `scripts/*.md`, `scripts/git-hooks/*`,
`archive/*/README.md`. **439 lines**, read by eye against one question: 「does
this state a RULE about where a probe lives, whether it is committed, or when it
is deleted?」

**What I excluded and why.** `agents/reports/`, `agents/briefs/` and
`archive/dev/` are FROZEN RECORDS; `dev/JOURNAL.md` and `dev/literature/` are
records too. **A record is not refreshed, it is corrected in the next
document.** `[LJ-1.130]`.

### 8.2 What I changed

| Site | What it said | Now |
|---|---|---|
| `dev/LESSONS.md:1055-1093`, **D-1** | 「A probe is never committed. Its home is the working tree」 | **Rewritten whole.** Section 9 quotes it |
| `dev/ORCHESTRATION.md:210` | 「D-1: probes are never committed」 | 「write the probe in `agents/reports/<TASK>/`, beside the report」. **This is the standing clause that reaches every brief** |
| `dev/ledger.toml:50` | 「Probes are NOT counted, because probe files are never committed」 | Section 12 |
| `dev/rules.toml:44`, the `probe` bundle | 「measures something in a scratch copy and throws it away」 | 「measures one thing and keeps the file as the report's other half」 |
| `dev/memos/working-mechanisms.md:52` | 「...and is thrown away」 | 「...and is KEPT」, pointing at D-1 |
| `dev/build-manifest.toml:13` | cited `check-probes.py:139-140` | `:20-23`. The line moved when the file shrank |
| `dev/ARCHIVE.md:70` | silent about four subtrees | a new section saying which archives its columns do NOT fit, and where each records itself |
| `scripts/README.md:196-231` | the whole lifecycle CLI, `--gate`, `--stale`, `make probes-sweep` | two commands, and the `ACMR` finding |
| `scripts/README.md:366` | `src/ProbeLJ197A.agda` | `agents/reports/LJ-1-97/ProbeLJ197A.agda` |
| `scripts/check-unbound-hyp.py:29,358` | `src/ProbeLJ197A.agda`, twice | the new path. **A live script citing a moved file** |
| `scripts/ledger.py:12-14, 97` | 「untracked by standing rule (D-1)」 | section 12's reason |
| `scripts/check-build-manifest.py:127` | 「Probe a report cites at a line number → `archive/probes/`」 | 「Probe → `agents/reports/<TASK>/`」 |
| `.gitignore:21` | 「Probes are throwaway by doctrine: never committed」 | a probe is TRACKED; what is ignored is a probe under `src/` |
| `Makefile:81-88` | two gate lines and `probes-sweep` | one gate line |
| `archive/README.md:16-33` | 「PROBES ARE ADMITTED」 | 「PROBES ARE NO LONGER HERE」 |
| `archive/probes/README.md` | the directory's rules | **a tombstone**, section 8.3 |
| `archive/tooling/README.md` | two scripts | three, with the retired lifecycle's record |
| `agents/README.md` | 「What is NOT here: **Probes**」 | 「**Probes live here**」, with the layout rule and the Agda name constraint |

### 8.3 What I reviewed and deliberately did NOT change

- **`dev/LESSONS.md:1688`**, 「the gate is a throwaway probe」. It prices ONE
  historical gate, it is not a rule about the lifecycle, and D-25's cost
  statement is true as written.
- **`dev/LESSONS.md:1659`**, `` `src/ProbeD10.agda` (untracked) ``. **A
  pre-existing DANGLING pointer.** `[LJ-1.133]` measured that the file was
  absent from `src/`, from `archive/probes/` and from its 283-probe index
  before it started, and left it visible as its own evidence. **It is now
  doubly wrong**, because 「untracked」 is no longer the vocabulary. **I did not
  edit a live rule's provenance line on my own reading**, following
  `[LJ-1.133]`. It needs an owner or orchestrator decision: drop it, or mark it
  lost.
- **`scripts/git-hooks/pre-commit:13-16`.** It calls `--staged`, whose signature
  did not change, so it is correct as written. **Out of my write scope.**
  MEASURED: it still exits 0.
- **`AGENTS.md:99`** and **`scripts/check-agents-guard.py:56`**,
  **`scripts/deletion-test.py:130`.** The first is about woven copies; the other
  two use `probe` as a local variable name.
- **The 216 briefs and 251 reports writing `src/Probe`.** Frozen records.

## 9. THE D-1 TEXT, which I wrote and the owner may correct

**I edited `dev/LESSONS.md` D-1** because the coordinator's message put it in my
EDIT list. The lifecycle block at `:1055-1077` is replaced by `:1055-1093`:

> **Where a probe lives (standing rule, owner-ruled 2026-08-13, replacing the
> lifecycle of 2026-08-04):** a probe is the REPORT'S OTHER HALF. The report
> carries the verdict; the probe carries the term, which no prose copies
> without loss. Both are evidence and both are kept.
>
> 1. **Write the probe in `agents/reports/<TASK>/`, beside the report.** One
>    directory per task, because a task often writes several probes. The
>    directory is the module qualifier, so the file declares
>    `module LJ-1-141.ProbeLJ1141A`. `bedrock.agda-lib` lists `agents/reports`
>    as an include root, so the probe imports the tower exactly as a master
>    does and **you run it where you wrote it. It never moves, so no citation
>    into it is ever rewritten.**
> 2. **NEVER under `src/`.** Thirteen probes were swept into a commit by a
>    `git add -A src/` on 2026-08-04, 3,274 lines, and had to be untracked.
>    `scripts/check-probes.py` is the gate, in `make check` and in the
>    pre-commit hook, because an ignore rule is a default that `git add -f`
>    walks past.
> 3. **The probe is TRACKED and is NEVER deleted.** Nothing sweeps it, nothing
>    archives it, and there is no clock on it.
> 4. **The report is still written, and it is still written first** (C-22). A
>    probe whose verdict is not in a report is not finished, however green it
>    is.
> 5. **Nothing typechecks a probe once its task closes.** It becomes text, like
>    the report, and its claim is true of the tree at its date. **So run it
>    yourself while your task is live: that is the only check it will ever
>    get.**
> 6. **A pattern worth keeping is not kept by keeping the file.** If a probe
>    taught a reusable shape, that shape belongs in this law book or in the
>    chapter it seeded. A tracked file is still not a home for a lesson.

**And the enforcement paragraph, because the coordinator asked for it by name:**

> **Enforcement points, because a rule with none is a wish.** Rule 2 is the only
> mechanical one: `scripts/check-probes.py --check` in `make check` and
> `--staged` in `scripts/git-hooks/pre-commit`, pinned by
> `scripts/tests/test_probe_gate.py`. **Rules 1, 3, 4, 5 and 6 are enforced by
> the brief and by the return audit** (`dev/ORCHESTRATION.md` section 1's
> standing clauses), and by nothing else.

**That last sentence is the honest part and I want the owner to see it.** The
old rule had a machine behind it in `--gate`. The new rule has a machine only
for 「not in `src/`」. **Rule 1's directory, rule 4's ordering and rule 5's
「run it yourself」 are enforced by a brief clause and a human audit.** Nothing
mechanical notices a probe written in the wrong directory, or a report whose
verdict was never written.

**A cheap check exists if the owner wants one**, and I did not build it because
nobody asked: a tracked `agents/reports/**/Probe*.agda` whose directory has no
matching report file is one glob. **Priced: about 15 lines in
`scripts/check-probes.py`, under a second.** It would catch a misfiled probe. It
cannot catch an unwritten verdict.

## 10. THE `AGENTS.md` LINES I PROPOSE, for the owner. DD19

**I did not edit `AGENTS.md`.** I read it fresh: **2,244 words against the 2,300
cap** in `scripts/check-dev-docs.py:105`, so there are 56 words of headroom.

**Site 1: the probe paragraph, `AGENTS.md:133-141`.** It is 105 words today and
carries three sentences that the ruling reverses. Proposed replacement, 99
words, so the cap gains 6:

> **Verify the load-bearing assumption cheaply before heavy or hard-to-reverse
> work.** Build the smallest decisive miniature and report GO or NO-GO with a
> price. A probe prices THIS setting; it never re-proves what the literature or
> the delivered tree settles. **Write it in `agents/reports/<TASK>/`, beside
> your report, and run it there.** It is tracked, it is never deleted, and
> **nothing typechecks it once your task closes, so run it while you can.**
> **`src/` is forbidden**, and `scripts/check-probes.py` enforces that because
> `git add -f` walks past an ignore rule. `dev/LESSONS.md` **D-1** is the rule.

**Site 2: the Never list, `AGENTS.md:49-50`.** It reads 「or probe files
(`src/Probe*.agda`)」. **MEASURED: this line is already correct**, because it is
scoped to `src/`, and `[LJ-1.133]` reported the same. **It is now MISLEADING,
which is a different defect**: a reader takes 「probe files」 as the class and the
parenthesis as an example. Proposed, and it saves one word:

> or a probe under `src/`

**Both edits need the owner's ruling and a dated `AGENTS-diff-approved:`
trailer** (DD19, `scripts/check-agents-guard.py`).

## 11. THE `dev/PLAN.md` DD8 SENTENCE I PROPOSE

**I did not edit `dev/PLAN.md`.** A sibling holds it, and a DD row is the
owner's.

`dev/PLAN.md:172`, inside DD8, reads:

> Nobody commits a probe.

**Proposed replacement, one sentence for one sentence:**

> A probe IS committed, in `agents/reports/<TASK>/` beside its report, and never
> under `src/` (`dev/LESSONS.md` D-1).

**One more PLAN site, and I flag it rather than propose an edit.**
`dev/PLAN.md:513`, the `LJ-1.57-A` row, carries 「A probe is never committed」
inside a verdict cell. **That is a section 11 row, which records what was found
on a date.** I read it as a frozen record and left it. If the owner reads
section 11 rows as live, it needs the same sentence.

## 12. THE LEDGER QUESTION: the answer is NO, and the reason changed

**The old justification evaporated and I agree with the coordinator's reading.**
`dev/ledger.toml:50` said 「Probes are NOT counted, because probe files are never
committed (D-1) and the script reads only git-tracked files.」 **Probes are
tracked now, so that sentence is false.**

**They are still not counted, and the surviving reason is the one that was
always doing the work:** this ledger counts the **DELIVERED PROOF**, which is
the in-fence code of a tracked `.lagda.md` master under `src/`. **A probe is
EVIDENCE, exactly as a report is evidence, and neither is proof.** A probe that
measured 395 lines contributes nothing to standing, which is correct.

**And the mechanism needs no exclusion rule.** MEASURED: `scripts/ledger.py:103`
runs over `src/**.lagda.md`, so `agents/` is outside the scan **by
construction**, not by a filter that somebody must remember to keep. **A rule
enforced by structure survives a ruling; a rule enforced by a filter does not.**

**MEASURED: `scripts/ledger.py --check` reports standing 28,617 over 85
masters, unchanged.** Both `dev/ledger.toml:50` and `scripts/ledger.py:12-14`
now state the surviving reason instead of the dead one.

## 13. TESTS AND CHECKERS

**`scripts/tests/test_probe_gate.py` is NEW, 51 checks, all pass.** It replaces
`test_probe_lifecycle.py`, which is archived with the machinery it tested.
`Makefile:171` names the new file.

| Group | What it pins |
|---|---|
| `src/` refused | 5 shapes, every depth and extension, plus the message |
| the home | `agents/reports/` accepted; 7 neighbouring paths refused |
| `.agdai` | refused in the exempt home too |
| non-probes | 4 real paths pass untouched |
| **the rename filter** | **`R` is in the filter, and a probe `git mv`-ed into `src/` is refused end to end** |
| the CLI | 8 retired flags exit 2 and none prints a success line |
| the live tree | every tracked probe is under `agents/reports/`; none under `src/` |

**The end-to-end gate test uses `GIT_INDEX_FILE` against a COPY of the index.**
`[LJ-1.133]` wrote a real file into `src/` and deleted it afterwards. **Mine
puts no file in `src/` and never touches the real index**, which also honours
the ruling that nothing is deleted.

| Checker | Result |
|---|---|
| `scripts/check-probes.py --check` | **exit 0**, 1,588 tracked files |
| `scripts/check-probes.py --staged` | **exit 0**, over 258 staged renames |
| `reuse lint` | **exit 0, 1,576 / 1,576** |
| `scripts/lint-prose.py --check` (whole tree) | **exit 0** |
| `scripts/check-tree.py --check` | exit 0, 87 masters, 7 subchecks |
| `scripts/check-dev-docs.py` | exit 0, 6 subchecks |
| `scripts/ledger.py --check` | exit 0, standing 28,617 unchanged |
| `scripts/check-build-manifest.py --check` | exit 0, 338 files, every one declared |
| `scripts/rules.py --check` | exit 0, 5 bundles, 141 lessons |
| `scripts/check-task-index.py` | exit 0 |
| **every suite in `scripts/tests/`** | **9 of 10 pass; the 10th is not mine** |

**The one red suite is `test_ratio_baseline.py`, and it is NOT mine. MEASURED.**
It fails 「the bucket EQUALS the cone: want 17185 got 20286」. It computes both
numbers from the live masters and the import graph. **My only change to
`dev/ledger.toml` is a comment block**, verified by `git diff` filtered to
non-comment lines, which is empty. A sibling holds `src/L/Condensation.lagda.md`.

**`scripts/check-rule-ids.py` reports 5 dangling references and NONE is mine.
MEASURED**: all 5 are in `scripts/README.md`, at bare `D20`, `D4` and `D18`
citations. The same text sits at `scripts/README.md:244` and `:483` in `HEAD`;
my edit shortened the file by 9 lines, so the numbers moved to `:235` and
`:474` and nothing else changed. **Out of my write scope for content; OWED.**

**I did not run `make check`.** The brief forbids it.

## 14. EVERY NEGATIVE, MARKED

- **MEASURED.** `agda agents/reports/LJ-1-141/ProbeLJ1141A.agda` exits 0 in
  1.22 s warm, `GHCRTS=-M8g`, one process, load average 5.0. A second include
  root with a `/` in its path works in THIS tree.
- **MEASURED.** `LJ-1-141` is a legal Agda module component; `lj-1.141`,
  `LJ-1_141` and `LJ_1_141` are `[ParseError]`. `.` splits the qualifier, `_`
  splits a mixfix name, and the trailing digits are then a literal.
- **MEASURED.** The interface lands at
  `_build/2.8.0/agda/agents/reports/LJ-1-141/`, never beside the source.
- **MEASURED.** `_build/2.8.0/agda/` gained a second subtree, `agents`, covered
  by `dev/build-manifest.toml:106`'s `2.8.0/**`.
- **MEASURED.** 258 probes now sit in 118 directories. `DD25` holds 55,
  `Unpaired` holds 12, `LJ-1-74` holds 10, and 113 directories hold 6 or fewer.
- **MEASURED.** 4 GREEN and 6 RED in a random sample of 10 archived probes,
  seed 1141, five REDs with `[FileNotFound]`. **The corpus had already rotted
  before any ruling.**
- **MEASURED.** 45 of 258 probes import another probe by its flat module name,
  several across task boundaries. That is why the historical probes were moved
  and not edited.
- **MEASURED.** 27 citations rewritten in live `dev/` documents; 30 paths
  resolve after brace expansion; 0 dangle.
- **MEASURED.** 257 staged probe renames, `--diff-filter=ACM` reported 0 of
  them and `ACMR` reported 254. The gate hole was live.
- **MEASURED.** The gate refuses a `src/` probe, accepts an `agents/reports/`
  probe, refuses an `.agdai` in the exempt home, and refuses a probe `git mv`-ed
  from its home into `src/`.
- **MEASURED.** `archive/probes/` was 8,664 KB over 257 files and 159,949 lines
  before the move; ten files carried 3.9 MB of it.
- **MEASURED.** A sibling wrote `src/ProbeLJ1136A.agda` at 15:06 today, under a
  frozen brief, while I emptied `src/` of probes. The gate still refuses to
  commit it.
- **MEASURED.** A proximity regex census MISSED 3 of the coordinator's 8 sites.
  Reading all 439 `probe` lines is what found the rest.
- **MEASURED.** `test_ratio_baseline.py` is red and my `dev/ledger.toml` diff
  contains no non-comment line.
- **MEASURED.** `check-rule-ids.py`'s 5 defects exist at `HEAD` with identical
  text.
- **INFERRED.** That no future module name collides between `src/` and
  `agents/reports/`. Today's risk is zero, MEASURED: no basename in
  `agents/reports/` matches one in `src/`. **It is a convention, not a gate.**
- **INFERRED.** That nobody wants to re-run a historical probe. If somebody
  does, `agda` refuses it with `[ModuleNameDoesntMatchFileName]` and names the
  module it wants. **This is the one cost the flat layout would not have had,
  and I am recording it rather than hiding it.**
- **INFERRED.** That `make check`'s wall time does not move. **I did not measure
  it**, because a sibling holds the Agda slot, and a number I did not measure is
  not a price (P-l). The mechanism is one more directory in the module search
  path.
- **INFERRED.** That `src/Everything.lagda.md` sees nothing new under a second
  root. It follows from Agda's search model, and my probe resolved 8 modules
  from `src/` with the second root live. **I did not run `make typecheck`.**
- **INFERRED.** That the census is complete. **439 lines were read by one
  reader against one question.** The pass-2 measurement proves a keyword search
  is not enough; it does not prove that reading is.

## 15. ARCHIVE USED

- **`agents/reports/lj-1.138-report.md`**, read WHOLE. Took: Part C's four
  measurements at `:241-288`, which I re-measured in this tree per P-l and which
  all reproduced; the decider at `:318-342` (216 frozen briefs), which the
  owner's design goes past rather than around; the `probes/README.md` draft at
  `:344-369`, whose warnings I moved into `agents/README.md`; and the gate's
  three honest limits at `:196-216`.
- **`agents/reports/lj-1.133-report.md`**, read WHOLE. Took: the
  verdict-versus-term split at `:8-12`, which is now D-1's opening sentence; the
  frozen-record ruling at `:105-110`, which decided that reports and briefs keep
  their old paths; **the two recall bugs at `:170-186` and `:462-476`**, which I
  handled and which did not bite because every family moved to one directory;
  the two-direction gate verification at `:145-153`, which I reproduced without
  writing into `src/`; and `:478-488`, the pre-existing `ProbeD10` dangler,
  still open.
- **`scripts/check-probes.py`**, read WHOLE before rewriting it. Took:
  `classify()`'s prefix-not-word discipline, the `.agdai` refusal, and the
  two-mode usage error. **Everything else is now
  `archive/tooling/check-probes-lifecycle.py`.**
- **`dev/LESSONS.md` D-1**, read WHOLE at `:1038-1077`. **Rules 1 and 3 are
  what the ruling reverses**; rule 2 (the report first) and rule 4 (a lesson is
  not kept by keeping a file) survive, renumbered 4 and 6.
- **`archive/probes/README.md`**, read WHOLE. Took its shorthand warning and the
  report-is-not-enough argument into the tombstone; the generated 257-row index
  became the tombstone's map, frozen.
- **`archive/README.md`**, read WHOLE. `:16-33` is what I replaced. `:37-47`
  (outside every gate) is why `archive/probes/` could never be typechecked, and
  MEASURED: `agda archive/probes/ProbeDD25CF.agda` fails in 0.10 s with
  `[ModuleNameDoesntMatchFileName]`.
- **`archive/tooling/README.md`**, read WHOLE, and its dashboard entry is the
  template my new section follows: what it was, why it went, what it did right
  from measurement, what it got wrong, last green, what would reopen it.
- **`dev/ARCHIVE.md:1-70`**, read. **Its columns index a retired Agda MODULE and
  do not fit a script**, which `[LJ-1.132]` and `[LJ-1.133]` both found. I added
  no entry row and instead made the registry say so.
- **`agents/README.md`**, read WHOLE. Its 「What is NOT here: Probes」 line was
  the most directly falsified sentence in the tree.
- **`REUSE.toml`**, read WHOLE. `agents/**` is CC BY-NC-SA through the carve-out
  at `:31-35`, so 258 moved probes needed **no entry**. MEASURED: `reuse lint`
  1,576 / 1,576.
- `dev/ORCHESTRATION.md:205-215`, `dev/rules.toml:43-45`, `dev/ledger.toml:44-56`,
  `dev/build-manifest.toml:8-18`, `scripts/README.md:196-231`,
  `scripts/git-hooks/pre-commit`, `Makefile`.

## 16. LITERATURE (DD18)

**Nothing in the literature governs a probe directory.**

## 17. TREE STATE

**Nothing committed. Nothing pushed.** The 258 probe moves are STAGED, because
`git mv` stages a rename and that is how git records a move without losing
history.

**Mine, staged:** 258 renames into `agents/reports/<TASK>/`;
`agents/reports/LJ-1-141/ProbeLJ1141A.agda` (new, tracked, the worked example);
`archive/tooling/check-probes-lifecycle.py` (new, the frozen snapshot);
`scripts/tests/test_probe_lifecycle.py` renamed to
`archive/tooling/test_probe_lifecycle.py`.

**Mine, modified:** `bedrock.agda-lib`, `.gitignore`, `Makefile`,
`agents/README.md`, `archive/README.md`, `archive/probes/README.md`,
`archive/tooling/README.md`, `dev/ARCHIVE.md`, `dev/LESSONS.md`,
`dev/ORCHESTRATION.md`, `dev/build-manifest.toml`, `dev/ledger.toml`,
`dev/rules.toml`, `dev/memos/working-mechanisms.md`,
`dev/memos/L3.30-rud-route.md`, `dev/memos/L3.32-below-lim-design.md`,
`scripts/README.md`, `scripts/check-probes.py`,
`scripts/check-build-manifest.py`, `scripts/check-unbound-hyp.py`,
`scripts/ledger.py`.

**Mine, new:** `scripts/tests/test_probe_gate.py` and this report.

**`REUSE.toml` needed no change**, MEASURED. **I created no top-level
directory.**

**NOT MINE, and I touched none of them:** `AGENTS.md`, `dev/PLAN.md`,
`dev/STYLE-agda.md`, `dev/literature/owner-notes-rud.md`,
`agents/reports/lj-1.136-report.md`, `src/ProbeLJ1134A.agda`,
`src/ProbeLJ1136B.agda`, and `scripts/check-dev-docs.py`,
`check-glossary.py`, `check-rule-ids.py`, `check-timing.py`, `check-tree.py`,
`lint-agda.py`, `lint-prose.py`, `weave-i18n.py`, all of which siblings modified
during my run.

**I did not delete one file.** **I ran Agda four times, one process at a time,
never above `-M8g`**, plus a 10-file sample that ran before the ruling arrived
and totalled 99.7 s. Load average stayed between 4.3 and 5.4.
