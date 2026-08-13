# LJ-1.142: one directory per task, holding its brief, its report and its probes

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## THE OWNER'S RULING, 2026-08-13

> 「现在简报和报告分在了两个文件夹里面，我希望你把它们合并成一个文件夹。我们今后
> 按这个子 agent 任务去划分子目录。也就是说，一个子 agent 任务建一个子目录，目录
> 里面放 brief、report 跟所有的探针。」

**One task, one directory, holding its brief, its report and every probe it
wrote.** The direction is RULED. **You make it work and you price it. Where the
implementation forks, surface it with a recommendation.**

This finishes what `[LJ-1.141]` started this afternoon. It moved 258 probes
into 118 task directories under `agents/reports/`. **Briefs stayed behind.**

## THE STATE, MEASURED by me before dispatch

| | |
|---|---|
| `agents/briefs/` | **415** files |
| `agents/reports/*.md` | **53** live reports |
| `agents/reports/archive/*.md` | **452** older reports |
| `agents/reports/<TASK>/` | **118** task directories, **258** probes |

**Naming is inconsistent across the three and you must handle all of it:**

- briefs: `LJ-1.136.md`, and also `t9-w7gate-brief.md`, `ifgp-brief.md`,
  `geology-legacy-brief.md`
- live reports: `lj-1.136-report.md`, lower case
- archived reports: `b1-report.md`, `b-gch-projection-recon.md`
- probe directories: `LJ-1-136`, dashes only

## THE CONSTRAINT THAT DECIDES THE NAMING, and it is already measured

**`bedrock.agda-lib` reads `include: src agents/reports`. A directory under an
include root becomes a MODULE NAME COMPONENT.**

`[LJ-1.141]` MEASURED this: **`LJ-1-141` works. `lj-1.141`, `LJ-1_141` and
`LJ_1_141` are all `[ParseError]`** because `.` splits the qualifier, `_`
splits a mixfix name, and trailing digits then read as a literal.

**So the directory name is not a free choice.** Re-verify it yourself, then
pick a rule that covers every task code in the corpus, including the ones with
no numeric code at all (`ifgp`, `t9-w7gate`, `geology-legacy`).

**If a task's files cannot be given one Agda-safe directory name, say so and
name the count. Do not invent a mapping nobody can reverse.**

## THE FORKS, each needs your recommendation

1. **Where does the merged tree live?** `agents/reports/` is now a wrong name
   for a directory holding briefs. `agents/tasks/` reads right. **But renaming
   the root changes `include:` and every citation.** Price both: rename the
   root, or keep `agents/reports/` and accept the name. **Say which and why.**
2. **The 452 archived reports.** Their tasks are from the retired route.
   **Do they get directories too, or does `archive/` stay flat?** Price it.
   **Consistency is worth something; 452 more directories is worth something
   too.** Recommend.
3. **A brief with no report, and a report with no brief.** Both exist. **Count
   them.** A directory with one file in it is fine; **an unpairable file that
   you cannot assign to a task is not, so name those separately.**
4. **The 20 non-report data files** that the owner deliberately left in
   `_build` at `[LJ-1.130]`, and anything else in `agents/` that is not a
   brief, a report or a probe. **Leave them where they are unless you can say
   why not.**

## THE EXPENSIVE HALF: citations

**Every `agents/reports/...` and `agents/briefs/...` citation in a live
document must follow.** `[LJ-1.141]` rewrote 27 and reports that
`[LJ-1.133]`'s two recall bugs did not bite it, for a structural reason.

**Count the citations BEFORE you move anything, and report the count.** Then
take these two, both MEASURED to have bitten before:

- **A brace family**, `Probe...{A,B,C,D}.agda`. A plain stem regex misses it.
- **A range shorthand**, `A..F`.

**`agents/` and `archive/` hold FROZEN RECORDS.** A brief or a report records
what was asked and what was found on its day. **Their CONTENT is never
rewritten. Only citations INTO them, from live `dev/` documents, are updated.**

## THE CONSUMERS, and C-40 says verify them

I grepped. **These read `agents/reports` or `agents/briefs` by path:**

```
scripts/check-build-manifest.py   scripts/check-dispatch-policy.py
scripts/check-dev-docs.py         scripts/check-rule-ids.py
scripts/check-probes.py           scripts/check-unbound-hyp.py
scripts/check-task-index.py       scripts/deletion-test.py
scripts/dd25-record.py            scripts/ledger.py
.gitignore                        Makefile
bedrock.agda-lib
```

**Thirteen. Every one must be checked and the ones that break must be fixed.**
`check-dispatch-policy.py` reads every brief to compare its `tier:` line
against the switch, so a path change silently drops its census to zero, and
**a checker that reads nothing prints green.**

## THE ABORT CRITERION

- **The merge lands and all thirteen consumers pass**: report and STOP.
- **A naming rule cannot cover the corpus**: **STOP AND SAY SO** with the
  count. That is a real finding.
- **The citation count is larger than you can verify**: say so, do the ones you
  can verify, and name what is left.
- **Anything walls**: STOP, report it.

## WHAT YOU MUST NOT DO

- **Do not rewrite the CONTENT of any brief or report.** Frozen records.
- **Do not delete anything.** Moves only.
- **Do not touch `src/ProbeLJ1134A.agda`, `src/ProbeLJ1136A.agda` or
  `src/ProbeLJ1136B.agda`.** They belong to a task that has not closed.
- **Do not weaken the `src/` gate** in `check-probes.py`.
- Do not edit `AGENTS.md`. DD19: propose the line, the owner rules. **It
  changed today; read it fresh, never from a report.**
- **Do not run Agda beyond the minimum the naming check needs**, and ONE
  process at the C-12 cap.
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## ARCHIVE (DD18)

- **`agents/reports/lj-1.141-report.md`**, read WHOLE. **The move you are
  finishing, its naming measurements, and the gate hole it found.**
- **`agents/reports/lj-1.133-report.md`**, read WHOLE. The citation rewriter
  and its two recall bugs.
- `agents/reports/lj-1.130-report.md`: the move that created `agents/` and
  rewrote 283 citations.
- `REUSE.toml`, read whole. `agents/**` is CC.
- `dev/ARCHIVE.md` and `archive/README.md`.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature governs a directory layout. Say so in one line.**

## SCOPE (read)

`agents/reports/lj-1.141-report.md` FIRST, then `bedrock.agda-lib`, then the
thirteen consumers above.

## SCOPE (write)

`agents/`, `bedrock.agda-lib`, `.gitignore`, `REUSE.toml`, `Makefile`,
`scripts/*.py`, `scripts/tests/`, and live `dev/*.md` for citations only. Your
report is your own task directory's report, and **you are the first task to
write into the new layout, so say what that felt like.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for rewrite` and read every
statement.

- **C-22.** Write the deliverable incrementally.
- **C-36.** Write the term you could not write.
- **C-39.** A brief's prohibition binds harder than its goal.
- **C-40.** Verify the CONSUMERS. **Thirteen are named above and a checker
  reading nothing prints green.**
- **P-l.** `[LJ-1.141]` measured in this tree; re-verify at your own site.
- **C-31, C-32, C-33, C-34, C-37, D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- **Add a test for every rule you change**, and **run the FULL
  `scripts/tests/` suite**, not only your own.
- `.venv/bin/python scripts/lint-prose.py --check` on everything you write.
- **Run every one of the thirteen consumers and show it.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with the layout you chose, the naming rule, and whether it covers the
whole corpus.** Then the counts: directories, files moved, citations rewritten,
unpairable files. Then the thirteen consumers, one line each. Then the forks
with your recommendation. Then what a reader gains and what they lose. **Mark
every negative MEASURED or INFERRED.**
