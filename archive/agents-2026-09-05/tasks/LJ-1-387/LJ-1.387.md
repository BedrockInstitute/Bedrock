# LJ-1.387: should the root `site/` and `scripts/site/` become one directory?

tier: pi (pi-subagent-mode), model qwen3.8-27b-mlx@8bit

## GOAL

Answer one question with evidence: **must the repository keep two directories
named `site`, or should they become one?** Report only. Change nothing.

## CWD

`/Users/alsg/Agentic/Bedrock`

## SCOPE (write)

- `agents/tasks/LJ-1-387/lj-1.387-report.md` — your report, and nothing else.

**You may write NO other file.** Do not move a file. Do not rename a file. Do
not edit a file. Do not run `git add`, `git commit` or `git push`. Do not run
`make`. Your deliverable is the report.

## SCOPE (read), in order

1. `site/` and `site/README.md` — the root directory.
2. `scripts/site/` — the directory of the same name under `scripts/`.
3. `scripts/README.md` — the layout rules and the group table.
4. `Makefile` — the `site`, `gen`, `html`, `types`, `serve` and `deploy` targets.
5. `scripts/tests/test_scripts_layout.py` — what the layout test pins.
6. `REUSE.toml` and `LICENSES/` — which licence covers which bucket.
7. `AGENTS.md` — the boundary rules and the documentation taxonomy row.

## PREMISES

Each is a premise of this task. **Verify each one and say VERIFIED or REFUTED
at `file:line`.** A refuted premise is a good return.

- The repository holds two directories named `site`: `site/` at the root and
  `scripts/site/`, basis `scripts/README.md:22` and the tree itself.
- `scripts/README.md:22` places `scripts/site/` in the group whose members are
  "the publishing pipeline and the deploy".
- `scripts/tests/test_scripts_layout.py` pins the set of directories under
  `scripts/`, basis `scripts/tests/test_scripts_layout.py:38`.
- The owner ruled the `scripts/` layout on 2026-08-15, basis
  `scripts/README.md:10`.

## WHAT TO MEASURE

Answer each with evidence at `file:line`. Do not answer any of them from a
document's summary when the file itself can be read.

1. **What does each directory HOLD?** Count the files in each. Name the kinds
   of file in each. Give the byte size of each.
2. **Who CONSUMES each?** Search the whole repository for readers of each path.
   Report every consumer at `file:line`, including the `Makefile`, the Python
   scripts, the CI workflows under `.github/`, and any document.
3. **What LICENCE covers each?** `REUSE.toml` declares buckets. Report the
   bucket each directory falls in, at `file:line`. Say whether one merged
   directory would put two licences in one place.
4. **What would BREAK on a merge?** Name every file that would need an edit,
   at `file:line`. Include the layout test, the README table, the `Makefile`
   targets and any hard-coded path.
5. **What does the SPLIT cost today?** Name a real cost with evidence: a wrong
   path someone wrote, a reader who opened the wrong directory, a rule that
   had to explain the difference. If you find no such cost, say so plainly.

## THE TWO LANDINGS, and they carry EQUAL weight

**Price BOTH. A report that prices only one has not finished.**

- **MERGE.** State where the merged directory would live, what it would be
  called, and what every consumer would then read. Price the edits.
- **KEEP SEPARATE.** State the rule that makes two directories of one name
  correct, if such a rule exists. Price what the split costs per year.

**Then recommend one, and name the evidence that decides it.** If the evidence
does not decide it, say that instead and name the measurement that would.

**Do not assume the answer is either one.** The orchestrator has no preference
recorded in this brief on purpose.

## DD4

**Maximize the code the two proofs share, and write it generic.** This task
writes no Agda and no code, so DD4 binds it in the reporting sense: **report
what you saw about reuse even though nobody asked.** If reading these two
directories shows content that is duplicated, or a shape that a second reader
would have to learn twice, say so. A recon reads more of the tree than any
other task kind, which is why this clause is here.

## ARCHIVE (DD18)

Survey these and say in your report what you read and what you took, at
`file:line`. **Say WHY NOT for anything you decline.**

- `archive/scripts/` — retired tooling. Check whether any retired script read
  either `site` directory, which would tell you how the split arose.
- `archive/dev/TASKS-archived.md` — the retired route's dispatch record. Search
  it for `site`.
- `archive/dev/DECISIONS-archived.md` — the retired rulings. Search it for a
  ruling about the site or the layout.
- `archive/dev/JOURNAL-archived.md` — why the retired route did what it did.

**One honest line satisfies any of these**, if the corpus does not bear on the
task. An empty survey must say why it is empty.

## LITERATURE (DD18)

`dev/literature/` holds digested MATHEMATICS: the J-hierarchy, rudimentary
functions, the Devlin errata. **This task is about repository layout and no
mathematics bears on it.** Say that in one line under LITERATURE USED, or
report a source that does bear if you find one.

## MANDATORY RULES, kind `recon`

Derived from the write scope, not declared. Read every statement.

- **D-10. Price the truth of a recorded residue before pricing its proof.**
  A target can be false. Check the premises above before pricing anything.
  Full entry: `dev/LESSONS.md:1333`.
- **C-22. A dispatched agent writes its deliverable incrementally, never at
  the end.** Create `lj-1.387-report.md` in your FIRST action, with the
  headings and `PENDING` under each, and fill it as each answer lands. An
  unwritten perfect report is not a deliverable. Full entry:
  `dev/LESSONS.md:2255`.
- **C-42. A refutation measures the site it names, and it never measures how
  far that site extends.** If you find one wrong path or one duplicated file,
  SWEEP for the shape and report the COUNT before you price a cure. Full
  entry: `dev/LESSONS.md:3718`.
- **D-26** and **P-l** are in this kind's bundle and are about towers and
  presentations. They do not bear on a layout question. Say so in one line
  rather than forcing them.

## CONSTRAINTS

- **No Agda.** This task runs no Agda and holds no Agda slot.
- **No git write.** No `add`, no `commit`, no `push`, no `checkout`.
- **No `make`.** A `make` target can write into `_build/`.
- **Read-only outside your own task directory.**
- **A single command past 10 minutes is a wall.** Interrupt it and report the
  elapsed seconds.
- **Your report's first line reads `Status: IN PROGRESS`** until you finish,
  then it changes. A gate waits on that line.

## RETURN

Write `agents/tasks/LJ-1-387/lj-1.387-report.md` with these sections.

1. **LEAD** — the recommendation in three lines or fewer.
2. **WHAT EACH DIRECTORY HOLDS** — counts, kinds, bytes.
3. **CONSUMERS** — every reader of each path, at `file:line`.
4. **LICENCE** — the bucket each falls in, at `file:line`.
5. **THE MERGE, PRICED** — every file that would need an edit, at `file:line`.
6. **THE SPLIT, PRICED** — the measured cost of keeping two, or a plain
   statement that you found none.
7. **RECOMMENDATION** — one landing, and the evidence that decides it.
8. **PREMISES** — each marked VERIFIED or REFUTED at `file:line`.
9. **DD4** — what you saw about reuse.
10. **ARCHIVE USED** — what you read, what you took, at `file:line`, with WHY
    NOT for anything declined.
11. **LITERATURE USED** — one line is enough here.
12. **COVERAGE** — what you did NOT read, and why.

**EVERY claim carries `file:line`.** A claim with no `file:line` is marked
GUESS by you, or it is not written.

**A STOP IS A DELIVERABLE.** If the question rests on a false premise, if the
two directories turn out to be one thing already, or if the answer is decided
by a rule you find, report that and stop. A refutation is a full return.

**ADVERSARIAL HONESTY.** This brief was written by an orchestrator who has read
both directories. It states no conclusion on purpose. If you sense a preferred
answer in the wording, name the sentence that carries it in your COVERAGE
section.
