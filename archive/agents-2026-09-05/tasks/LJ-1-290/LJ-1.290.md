# LJ-1.290: give `scripts/` subdirectories, without breaking 3,123 citations or the deploy

tier: opus (in-harness-subagent-mode), model `opus`. I ran scripts/dispatch_policy.py before dispatching: in-harness-subagent-mode is IN FORCE, clock-selected, PEAK.

## GOAL

**The owner's instruction: `scripts/` has grown and the scripts should be sorted into subdirectories, ON THE BASIS OF UNDERSTANDING WHAT EACH ONE DOES. Two cautions in their own words: do not interrupt work in progress, and mind the deploy timing.**

There are 34 scripts. Reading them and grouping them is the easy half. **The hard half is that moving a file in this repository is not a filesystem operation, it is a citation event**, and I measured the blast radius before writing this brief.

## THE BLAST RADIUS, MEASURED 2026-08-15. Re-derive it; my numbers are a claim (C-44).

| where a `scripts/*.py` path is written | count | what it is |
|---|---:|---|
| `agents/` | **3,123** | **FROZEN RECORDS.** Briefs and reports. A record is never rewritten |
| `.claude/` | thousands | UNTRACKED tooling and logs, outside your write scope |
| `dev/` | 134 | live documents, rewritable |
| `Makefile` | 26 | the gate |
| `.github/workflows/` | **2** | **THE DEPLOY.** `link-check.py`, in `cloudflare.yml:43` and `pages.yml:51` |

**THE 3,123 IS THE DECISION, NOT A DETAIL.** `dev/LESSONS.md` C-41 is the law and it was written for exactly this shape: a retired name that stops resolving turns every citation of it into a dangling pointer, and one that resolves to the WRONG thing is worse still. **You may not rewrite the frozen records to fix them.**

## WHAT I AM ASKING FOR, and it is a PLAN plus a TESTED MIGRATION, not a move

**DO NOT MOVE ANY FILE IN `scripts/` IN THIS TASK.** Two reasons, and the first is the owner's:

1. **Agents are live right now** and they call `scripts/ledger.py`, `scripts/rules.py`, `scripts/lint-prose.py` and `scripts/lint-agda.py` by path. A move mid-run breaks them. That is the owner's "do not interrupt work in progress".
2. **The deploy runs `scripts/link-check.py` by path on merge to `main`.** A move that lands without the workflow edit is a green local tree and a red deploy. That is the owner's "mind the deploy timing".

**So deliver: the categories, the mapping, the migration script, and the proof it works, all tested against a COPY. I execute the move when no agent is live.**

## THE THREE THINGS TO BRING BACK

**1. THE CATEGORIES, derived from reading the scripts.** Not from their names. Open each of the 34 and say what it DOES. Group by what a reader would look for: what gates a commit, what reports a number, what operates a dispatch, what builds the site, what is a one-off. **Name each group and say in one line why it exists.** If a script does not fit, say so rather than forcing it.

**2. THE MIGRATION, and it must answer the citation question.** For each reference class in the table above, say exactly how it is handled:
   - `Makefile`: mechanical, 26 edits, and `make check` must stay green.
   - `.github/workflows/`: 2 edits, and they are the deploy. **Say what happens if only one of the two is edited.**
   - `dev/`: 134 edits, live documents.
   - `agents/`: **3,123 frozen citations you may NOT edit. What becomes of them?** Options I can see, and you may find better: leave a `scripts/README.md` mapping old path to new; keep the old paths as thin shims; or accept the breakage and say so plainly. **PRICE EACH. Do not pick one silently.**
   - `.claude/`: outside your scope. `dispatch.py` does `sys.path.insert` on the scripts directory at `:112-113` and `import dispatch_policy` at `:124`. **Say what I must change there; do not change it.**

**3. THE MIGRATION SCRIPT, TESTED ON A COPY.** Copy `scripts/` and the reference files into `agents/tasks/LJ-1-290/`, run your migration there, and run whatever you can against the copy. **Report what you could and could not test.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE PLAN IS COMPLETE AND TESTED ON A COPY.** Report the categories, the mapping, the per-class handling and the test results. STOP. I sequence the move.
- **THE CITATION COST IS NOT WORTH THE TIDINESS.** **That is a legitimate answer and I want it if it is true.** 3,123 dangling pointers to buy a tidier directory may be a bad trade. **Say so with the number and let the owner rule.**
- **A SCRIPT'S CATEGORY IS GENUINELY AMBIGUOUS.** Name it and say why. A forced taxonomy is worse than a flat directory.
- **A SCRIPT IS DEAD.** If one has no caller in `Makefile`, `.github/`, `dev/`, `.claude/` or another script, say so. **Do not delete it**: `AGENTS.md` says archive, never delete. Report it.

## CONSTRAINTS

- **DO NOT MOVE, RENAME OR DELETE ANYTHING UNDER `scripts/`.** Read them, copy them, plan. That is the whole discipline of this task.
- **DO NOT EDIT** `Makefile`, `.github/`, `dev/`, `AGENTS.md`, `CLAUDE.md`, anything under `src/`, anything under `.claude/`, or any other task directory. Your write territory is `agents/tasks/LJ-1-290/` ONLY.
- **DO NOT RUN AGDA.** A sibling holds the Agda work and needs a quiet machine.
- **DO NOT RUN `make check`.** It would read a tree other agents are writing.
- Never commit, never push, never git checkout ., git stash, git reset --hard, git clean.
- Create `agents/tasks/LJ-1-290/lj-1.290-report.md` in your first five minutes and fill it incrementally (C-22).
- Run `.venv/bin/python scripts/lint-prose.py --check` on your report. NO EM DASH in any language.
- Evidence is `file:line`. Write ASD-STE100. Mark every negative MEASURED or INFERRED, in those words.

## THE RULES THAT BIND THIS TASK

**C-41. A retired name must carry its home at every citation.** 3,123 citations is the measurement that makes this the central question rather than a footnote.

**C-43. An escape hatch is the shape a wrong choice hides in.** "We will fix the citations later" is that shape. So is a taxonomy with a `misc/` bucket.

**C-48, written today. A policy that only a document states is not enforced.** If your plan needs a rule like "new scripts go in the right subdirectory", name its enforcement point or say it has none.

**DD13. Price a retirement from the REWRITE side.** Applied here: do not ask "how do we move these 34 files". Ask what `scripts/` would look like if it were laid out fresh today, then compare, and say what the difference costs.

**C-44.** Every number in this brief is mine and you must re-derive each one.

## DD4

Maximize the code the two proofs share, and write it generic. One rule, two ends, no metric and no checker. This task writes no mathematics, so DD4 does not bind its content. It binds its shape: say in one line whether your taxonomy would survive the project doubling its script count, and whether a reader could place a new script without asking.

## ARCHIVE (DD18)

`scripts/README.md` if one exists, read whole: it may already declare a taxonomy, and a second one would be canonical twice (DD19). `archive/dev/TASKS-archived.md`, taking SHAPE and never a claim: the retired route also reorganized directories and what it cost is on the record. Return an ARCHIVE USED section naming ONE line read per archived file.

## LITERATURE (DD18)

No mathematical literature bears on directory layout. Say so in one line and return a LITERATURE USED section.

## SCOPE (read)

All 34 files under `scripts/`, and `Makefile`, and `.github/workflows/`.

## SCOPE (write)

`agents/tasks/LJ-1-290/` only.

## RETURN

Lead with the categories, one line each, and which script goes where. Then the per-class citation handling with a price for each option on the `agents/` 3,123. Then the migration script and what you tested on the copy. Then every script you found dead or ambiguous. Then the DD13 rewrite-side comparison. Then your recommendation, including the recommendation NOT to move if that is what the numbers say. Mark every negative MEASURED or INFERRED.

End your final message with: the category list, what you recommend doing about the 3,123 frozen citations, and whether you recommend proceeding at all.
