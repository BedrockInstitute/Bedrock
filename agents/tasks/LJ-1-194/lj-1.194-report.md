# LJ-1.194 report: P4, the DD number-uniqueness check

tier: pi (deepseek-subagent-mode), model deepseek-v4-flash. Write scope:
`scripts/check-rule-ids.py`, `scripts/tests/test_rule_series.py`, and this
report. Nothing else. No Agda ran. No dispatch was made. No commit, no push.

## 0. LEAD

The three runs, first. Each is MEASURED.

1. **The real tree passes.** `python3 scripts/check-rule-ids.py` prints
   `check-rule-ids: clean (45 files, 145 lessons, 67 decisions)` and exits 0.
   The uniqueness check is live inside that run.
2. **A synthetic duplicate fails.** A patched read feeds two `| DD27 |` rows,
   the exact shape commit `142637c` minted. The CLI prints a `DEFECT:` line
   for `DD27` and exits 1.
3. **The test pins both.** `python3 scripts/tests/test_rule_series.py` runs 72
   checks. All pass. The exit is 0. Nine of the checks are new and test the
   uniqueness check.

**No real duplicate exists today.** MEASURED, at the row census in section 4
and by the clean run. The abort criterion's second case does not fire.

**The LESSONS series has no legitimate repeat.** MEASURED:
`duplicate_lessons()` returns empty over 145 headings. The abort criterion's
third case does not fire. No scoping is needed.

## 1. What was built

`scripts/check-rule-ids.py` gains one function and one refactor.

- `duplicate_codes(codes)` at `:202`. It counts the codes it receives and
  returns the ones that appear more than once. This is the ONE counting path
  for every series.
- `duplicate_lessons()` at `:216` now calls it. Its behavior is unchanged.
  The six LESSONS prefixes, P, R, T, I, D, C, already share one heading regex.
  One path serves all six.
- `duplicate_decisions()` at `:228` is the new check. It reads the `DD` rows
  from `dev/PLAN.md` with the existing `DD_ROW` regex at `:84`. It reads the
  `D` rows from `archive/dev/DECISIONS-archived.md` with the existing
  `PLAN_ROW` regex at `:75`. It counts each series separately and returns one
  finding per duplicate code.
- `main()` at `:376` prints each finding with a `DEFECT:` prefix and exits 1.

**The series boundary is the file.** `DD5` and the archived `D5` are different
codes. Both may exist. The check never counts across the two files. MEASURED
by the probe in section 5.

**The consolidated and revoked codes are structurally excluded.** They are
preamble prose, never table rows. The row regexes cannot match them. They
still resolve, on purpose, and they are not defects. MEASURED.

## 2. The three runs, in full

### 2.1 The real tree

Command: `.venv/bin/python scripts/check-rule-ids.py`.

Output: `check-rule-ids: clean (45 files, 145 lessons, 67 decisions)`.

Exit: 0. MEASURED.

### 2.2 The synthetic duplicate

Command: the module in-process, with `cri.PLAN` patched to a text holding two
`| DD27 |` rows and one `| DD24 |` row. The patch writes nothing to the tree.

Output: a `DEFECT:` line reading "`DD27` appears in 2 rows of the `DD` series
(dev/PLAN.md section 3), and PLAN's preamble says a number is never reused in
either series. A `DD` row is the owner's (DD0): report the duplicate, never
fix it."

Exit: 1. MEASURED.

### 2.3 The test

Command: `.venv/bin/python scripts/tests/test_rule_series.py`.

Output: 72 checks marked ok, ending with `test_rule_series: all checks
passed`. The new section, "the uniqueness check", runs 9 checks. Exit: 0.
MEASURED.

## 3. What the check cannot see

Each claim about machine behavior is marked.

- **A replacement is invisible.** If the older row is removed and a different
  row takes the number, one row remains and the check is clean. MEASURED: the
  probe with one `DD27` row returns no finding. The minted episode was
  visible only because both rows stood at once.
- **A suffix code is invisible.** `DD27a` beside `DD27` returns no finding.
  MEASURED. A suffix makes the code a different string.
- **A spaced row is invisible.** `| DD 27 |` does not match the row regex.
  MEASURED.
- **A three-digit code is invisible.** `DD100` does not match `DD\d{1,2}`.
  MEASURED. This limit predates this task.
- **Which row is the rule is not decided.** The check reports the pair. It
  never names the older row as the winner. DD0 makes a `DD` row the owner's.
  The message says "report, never fix" on purpose.
- **Series outside these four are untouched.** Task codes and other numbering
  series do not resolve here. They were never in scope.

## 4. The searches I ran, by shape

The trap named in the brief is a search that excludes what it looks for. Every
sweep below is by SHAPE. Each shape used two mechanisms.

1. **Row shape in PLAN.md.** `grep -n "^| DD" dev/PLAN.md`, a `uniq -d` pass
   on the code column, then the checker's own `DD_ROW` in-process. The two
   agreed: 19 `DD` rows, no duplicate.
2. **Row shape in the archive.** `grep -n "^| D[0-9]"` on the archived file,
   a `uniq -d` pass, then `PLAN_ROW` in-process. The two agreed: 32 `D` rows,
   no duplicate.
3. **Heading shape in LESSONS.** `duplicate_lessons()` in-process over 145
   headings. No duplicate.
4. **The suffix shape.** `DD25-GAP` checked separately, because a suffix is a
   different code. It is a task-index row, not a `DD25` row.
5. **The episode shape.** `git log -S "DD27" -- dev/PLAN.md`, then `git show`
   on `142637c` and `cda4619` to read the mint and the strike.

No filter removed a candidate file. Every count came from the full shape, not
from one spelling that could miss a twin.

## 5. The behavior probes

`duplicate_decisions` takes its texts as parameters. A test can feed synthetic
text without writing to the tree. This is the same design as `series_findings`.

| input | result |
|---|---|
| real PLAN.md and real archive | no finding, MEASURED |
| two `DD27` rows, one `D5` row | `DD27` finding, MEASURED |
| two `D27` rows, one `DD5` row | `D27` finding, MEASURED |
| `DD5` and `D5`, one each | no finding, MEASURED |
| consolidated prose codes only | no finding, MEASURED |
| `DD25` and `DD25-GAP` | no finding, MEASURED |
| one `DD27` row only | no finding, MEASURED |
| `DD27a` beside `DD27` | no finding, MEASURED |
| `| DD 27 |` beside `DD27` | no finding, MEASURED |
| two `DD100` rows | no finding, MEASURED |

## 6. DD4

The counting logic is ONE code path. `duplicate_codes` at `:202` is the only
place that counts. Three consumers feed it: the LESSONS headings, the `DD`
rows, and the `D` rows. A check written per series would have been paid five
times. This one is paid once. The per-series difference is only which rows
feed the counter, never how the counter counts.

## ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-189/lj-1.189-report.md`, read whole. Took section 7,
  "P4: the DD number-uniqueness check", at `:263-273`: the proposal, the
  commit hashes, and the sentence "uniqueness is mechanical in a way intent
  is not". Took section 8, which names what has no cure, so this report
  promises none.
- `scripts/check-rule-ids.py`, read whole. Took the existing parsing as the
  only admissible source: `DD_ROW` at `:84`, `PLAN_ROW` at `:75`,
  `known_decisions()` at `:271`, `duplicate_lessons()` at `:216`, and the
  series scope that scans `scripts/*.py`. That scope is why the new
  docstrings write the `archived` home beside every bare `D` code.
- `scripts/tests/test_rule_series.py`, read whole. Took the `check()` harness
  at `:41`, the FAKE path label at `:51`, and the no-write philosophy: a
  function takes its text, a test never edits the tree.
- `dev/PLAN.md` section 3 preamble at `:238`: "A number is never reused, in
  either series", and the consolidated and revoked paragraph at `:240`, which
  says those codes still resolve.
- `archive/dev/DECISIONS-archived.md` at `:14` and `:25`: the `D` series never
  reuses a number, and the struck codes still resolve.
- `dev/LESSONS.md` C-32 at `:2965`, C-39 at `:3539`, C-40 at `:3620`, C-41 at
  `:3657`, C-42 at `:3704`, C-43 at `:3758`, read whole. C-41 is the
  load-bearing law: a resolution check cannot see intent, which is this
  task's defect one level down. C-42 is the sweep law, which section 4
  follows.
- Commits `142637c` (the minted duplicate row) and `cda4619` (the strike,
  with the self-admission "AND I MINTED A DUPLICATE NUMBER").

## LITERATURE (DD18)

Not this task's subject. Nothing in `dev/literature/` bears on a number
uniqueness check; DD18 is satisfied by this one honest line.
