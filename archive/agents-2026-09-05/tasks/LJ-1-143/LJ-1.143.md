# LJ-1.143: split the DD25 bucket, retire `archive/probes/`, and make `archive/` mirror the root

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## THE OWNER'S RULING, 2026-08-13

> 1. 把 DD25 的内容按写它们的那次审查拆回各自的任务目录
> 2. 退役 `archive/probes/`
> 3. **archive 需要复刻根目录的结构，不然会越来越乱的。** 比如：你本来从
>    `dev/measurement` 归档的东西，那就要放在 archive 里面的 `dev/measurement`
>    里面，而不能裸露。对于 source 也是一样，现在出现了两个这一类的文件夹，应该
>    全部放到一个 `src` 文件夹里面，通过文件夹的名字标明是哪次的归档。

**Three tasks. All three are RULED. You make them work; you do not re-litigate
them.**

## TASK 1: split `agents/tasks/DD25/`

**55 probes sit there.** `[LJ-1.142]` refused to place them and its reason was
sound: DD25 is a RULING, not a task, so the names carry no task code, and **a
citation records who CITED a file rather than who WROTE it.**

**The owner has now ruled they be placed. So find the WRITER, and the evidence
is inside the files.**

**MEASURED by me before dispatch, and it is only a start:** 16 of the 55 carry
their origin in a header comment, in this shape:

```agda
-- [DD25 / LJ-1.41 REVIEW] DOES A Δ₀ WITNESS EXIST FOR A TWO-WAY ...
```

That gives LJ-1.27 (7), LJ-1.41 (4), LJ-1.50 (3), LJ-1.32 (1), LJ-1.33 (1).
**39 did not match my regex, which read only the first twelve lines and only
two patterns. Yours must do better.** Read the whole header, and read the body
when the header is silent: a probe names the module it is testing and quotes
the return it is attacking.

**The second source is the reviews themselves.** A DD25 review is a report; it
says what it wrote. `agents/tasks/archive/LJ-1-33/lj-1.33-review.md` exists.
**Find every DD25 review in the corpus and read what each says it built.**

**THE RULE FOR A PROBE YOU CANNOT PLACE ON EVIDENCE: leave it in `DD25/` and
name it.** `[LJ-1.142]` was right that a guess is worse than a bucket. **An
honest residue of eight is a success; a wrong placement is unrecoverable
because the evidence for the original pairing is the thing you overwrote.**

**Report, for each probe: the task you placed it in, and the `file:line` that
proves it.**

## TASK 2: retire `archive/probes/`

It holds **one file**, `README.md`, a tombstone mapping 257 old paths. Every
probe left for `agents/tasks/`.

**`[LJ-1.141]` wrote that tombstone when the root was `agents/reports/`.
`[LJ-1.142]` then renamed the root to `agents/tasks/`, so the tombstone is one
hop short. `[LJ-1.142]` recorded that as OWED.**

**Decide what a retired tombstone is for, and act on your answer.** If a live
document still cites an `archive/probes/` path, the tombstone must keep
resolving it and must be CORRECT through both hops. **If nothing cites it, say
so MEASURED and retire the directory into wherever task 3 puts it.**

**`dev/ARCHIVE.md` records what a retirement carries:** what it was, why it
left, where it was last green, **what it did right from measurement rather than
praise**, and what would reopen it.

## TASK 3: `archive/` mirrors the root

**The owner's reason is drift**, and it is the same reason that produced three
defects this session: a flat bucket with no structural rule fills up and then
nobody can tell where anything came from.

**The root is:**

```
_build/  agents/  archive/  dev/  docs/  LICENSES/  scripts/  site/  src/
```

**`archive/` today is:**

| | files | |
|---|---:|---|
| `archive/dev/` | 5 | the retired records. **Already correct** |
| `archive/rud-route/` | 74 | |
| `archive/src/` | 25 | |
| `archive/measurements/` | 9 | **the owner names this one: it came from `dev/measurements/`, so it belongs at `archive/dev/measurements/`** |
| `archive/tooling/` | 7 | |
| `archive/kits/` | 6 | |
| `archive/probes/` | 1 | task 2 |

**THE RULE: an archived thing sits at the same path under `archive/` that it
had under the root.** Something archived from `dev/measurements/` goes to
`archive/dev/measurements/`. Something archived from `scripts/` goes to
`archive/scripts/`.

**FIND THE PROVENANCE, do not guess it.** `git log --diff-filter=A` and
`--follow` give the original path of every file. **Report the provenance you
found for each of the six directories, at `file:line` or at a commit.**

**THE SOURCE CASE, which the owner names explicitly.** `archive/rud-route/`
and `archive/src/` are both archived source. **They become ONE `archive/src/`,
and the DIRECTORY NAME says which archival it was.** Choose the naming and say
why; the owner asked for「通过文件夹的名字标明是哪次的归档」, so the name must
identify the archival event, not merely the content.

**If a directory's provenance is genuinely unclear, leave it, list it, and say
what would decide it.**

## THE COST YOU MUST MEASURE FIRST

**All three tasks move files, so all three break citations.** `[LJ-1.142]`
rewrote 358 across 36 files.

**COUNT THE CITATIONS BEFORE YOU MOVE ANYTHING and report the count.** Then
take these three, all MEASURED to have bitten a sibling this session:

- **A brace family**, `Probe...{A,B,C,D}.agda`. A plain stem regex misses it,
  and it bit `[LJ-1.133]` and `[LJ-1.142]` on the SAME `dev/LESSONS.md` line.
- **A range shorthand**, `A..F`.
- **A `Path`-style construction in a checker**, invisible to any string-level
  rewriter. `[LJ-1.142]` found five and wrote `scripts/agents_tree.py` for
  them. **Read it before you assume a grep is a census.**

**Run a DRY RUN that prints what it cannot resolve.** That is the only reason
`[LJ-1.142]` caught its own recall bug.

## THE CONSUMERS, and C-40 says verify them

`[LJ-1.142]` found **fourteen**, one more than I grepped, and the extra one
(`scripts/check-sources-read.py:45`) **is not in `make check`**:
`dev/ORCHESTRATION.md:460` runs it by hand after every dispatch, so it fails
silently. **Its list is in `agents/tasks/LJ-1-142/lj-1.142-report.md`. Run all
fourteen and show each.**

## THE ABORT CRITERION

- **All three land and all fourteen consumers pass**: report and STOP.
- **A DD25 probe cannot be placed on evidence**: **leave it, name it.** That is
  the correct outcome, not a failure.
- **A directory's provenance cannot be established**: same.
- **Anything walls**: STOP, report it.

## WHAT YOU MUST NOT DO

- **Do not guess a pairing or a provenance.** `[LJ-1.142]` declined to place 9
  of 12 files it could have placed from a citation column, and it was right.
- **Do not delete anything.** Moves only, as git renames.
- **Do not rewrite the CONTENT of a brief, a report or a probe.** Frozen
  records. **The header comment inside a probe is evidence; read it, never
  edit it.**
- **Do not touch `src/ProbeLJ1134A.agda`, `src/ProbeLJ1136A.agda` or
  `src/ProbeLJ1136B.agda`.** Their task has not closed.
- **Do not weaken the `src/` gate** in `check-probes.py`.
- Do not edit `AGENTS.md`. DD19: propose the line, the owner rules. **It
  changed twice today; read it fresh.**
- **Do not run Agda** unless a directory name forces it, and then ONE process
  at `GHCRTS="-A64m -I0 -M8g"`.
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** 「Nothing cites this」 is MEASURED
only if you ran the search and say which search.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-142/lj-1.142-report.md`**, read WHOLE. The merge you are
  extending, its fourteen consumers, its naming rule and its recall bug.
- **`agents/tasks/LJ-1-141/lj-1.141-report.md`**, read WHOLE. The tombstone you
  are retiring and why it is one hop short.
- `agents/tasks/LJ-1-133/lj-1.133-report.md`: the citation rewriter and the
  brace-family bug.
- **`dev/ARCHIVE.md`**, read WHOLE, and `archive/README.md`. **What an archival
  record must carry, and it is the standard for task 2 and task 3.**
- `scripts/agents_tree.py`, read WHOLE.
- `REUSE.toml`, read whole.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature governs a directory layout. Say so in one line.**

## SCOPE (read)

`agents/tasks/DD25/` whole, FIRST. Then `agents/tasks/LJ-1-142/lj-1.142-report.md`.
Then `git log --diff-filter=A` for each of the six archive directories.

## SCOPE (write)

`agents/tasks/`, `archive/`, `scripts/*.py`, `scripts/tests/`, `dev/*.md` and
`dev/memos/*.md` for citations only, `dev/ARCHIVE.md` for the retirement
records, `.gitignore`, `REUSE.toml`, `Makefile`. Your report is
`agents/tasks/LJ-1-143/lj-1.143-report.md`.

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for rewrite` and read every
statement.

- **C-22.** Write the deliverable incrementally.
- **C-36.** Write the term you could not write: **name every probe and every
  directory you could not place.**
- **C-39.** A brief's prohibition binds harder than its goal.
- **C-40.** Verify the CONSUMERS. **Fourteen, one outside `make check`.**
- **C-31, C-32, C-33, C-34, C-37, D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- **Add a test for any rule you add**, and **run the FULL `scripts/tests/`
  suite**, not only your own.
- `.venv/bin/python scripts/lint-prose.py --check` on everything you write.
- **Run all fourteen consumers and show each.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with the three counts: DD25 probes placed and left, directories moved,
citations rewritten.** Then the DD25 table: probe, task, and the `file:line`
that proves it. Then the provenance of each archive directory. Then the
`archive/` tree as it now stands. Then the fourteen consumers, one line each.
Then anything you could not place. **Mark every negative MEASURED or
INFERRED.**
