# LJ-1.208 report: gate DD25, because the orchestrator forgets it

tier: pi (deepseek-subagent-mode), model deepseek-v4-flash. Work touched no
Agda code. No Agda ran, no commit, no push. Every behavioural claim is marked
MEASURED or INFERRED.

## 0. THE THREE RUNS

### 0.1 The real tree passes, with the backlog counted. MEASURED

Command: `.venv/bin/python scripts/check-dd25-review-named.py`

```
check-dd25-review-named: 285 index rows, 42 frozen pre-epoch negative
row(s) without a named review, 0 new defects; backlog: 42 pre-epoch
row(s) negative with no named review, frozen: LJ-0.4b, LJ-0.4c, ...
```

Exit status 0. The backlog is **42 rows**: that many index rows carry a
negative verdict in the verdict cell and name no review code. That is the
honest scale of the lapse. MEASURED (the run's own output).

### 0.2 A synthetic negative row without a review code fails. MEASURED

A synthetic row `LJ-9.99` with verdict `NO-GO: the band does not fit` and no
review citation was spliced into a copy of the live task index, and the
checker was pointed at the copy with `--plan`. Output, verbatim:

```
check-dd25-review-named: 1 row(s) fail DD25, 42 frozen pre-epoch:
  DD25 unmet: row LJ-9.99 carries the negative verdict "NO-GO: the band
  does not fit" (tokens: NO-GO, DOES NOT) and names no DD25 review.
  DD25 requires the row to name its review's code. Append the review's
  verdict with its code, e.g. `DD25 review [LJ-x.y] UPHELD`, or write
  `DD25 review not needed: <reason>` in the row if this verdict is not
  a DD25 negative.
```

Exit status 1. The message names the row, quotes the verdict, and says what
to do. MEASURED (the run's own output).

### 0.3 A row that names its review passes: the four controls. MEASURED

`LJ-1.162` (`DD25 review [LJ-1.182] UPHELD`), `LJ-1.165` (`[LJ-1.181]`),
`LJ-1.169` (`[LJ-1.179]`) and `LJ-1.172` (`[LJ-1.180]`) all clear the gate.
Also clears: `LJ-0.4f` (bare `LJ-0.4f-R`), `LJ-1.15` (bare `LJ-1.15-R`),
`LJ-1.16` (bare `LJ-1.16-R`), `LJ-1.50` (abbreviated `1.50-R`) and `LJ-1.10`
(bare `LJ-1.11`, whose own row is an adversarial review). The test suite
asserts all four controls against the real tree. MEASURED.

## 1. THE NEGATIVE-VERDICT VOCABULARY, AS A TABLE

`scripts/check-dd25-review-named.py` carries the table at module level, as
`NEGATIVE_VERDICT`, with one row per token, a match mode, and a reason. The
next rule that needs "what counts as a negative" reads this table instead of
reinventing it. The table, verbatim:

| token | match | why it announces a negative |
|---|---|---|
| STOP | prefix | a stop taken as the deliverable is DD25's trigger |
| NO-GO | word | a NO-GO is DD25's trigger by name |
| REFUTED | word | a refutation of the brief's premise is DD25's trigger |
| REFUTABLE | word | a refutation of the brief's premise is DD25's trigger |
| REFUSED | word | DD25's trigger names a refusal; the verdict spells it |
| REFUSAL | word | DD25's trigger names a refusal; the verdict spells it |
| BLOCKED | word | a landed result that cannot land is a negative |
| FALSE | word | a stated fact found false is a refutation |
| WALL | prefix | a wall is a landed result that misses its band floor |
| OVERTURNED | word | a negative overturned still announces the negative |
| DOES NOT | word | a theorem that does not derive is a refutation |
| NOTHING | word | a deliverable that proves nothing is a negative |
| ZERO | word | a zero-line result is a stop or an unbuilt claim |

`word` means `\b<token>\b`; `prefix` means `\b<token>`, so `STOP` catches
`STOPPED` and `WALL` catches `WALLS`, both measured in verdict cells.

**The owner's ten, plus three, and each addition is a row with a reason, so
each can be ruled down by deleting a row.** DD25's trigger names "a refusal"
and "a refutation" in as many words, and the shorthand list omitted those
spellings: `REFUSED`, `REFUSAL` and `REFUTABLE` are real verdicts on the real
tree (`LJ-0.4b`, `LJ-0.4e`, `LJ-1.38`, `LJ-1.16`, `LJ-1.84`, `LJ-1.121`),
all pre-epoch. INHERITED from the owner's brief for the ten; the three
additions are INFERRED from DD25's trigger sentence and are the tunability
the brief asks for.

## 2. WHAT THE GATE CANNOT SEE, QUOTED FROM ITS OWN DOCSTRING

From `scripts/check-dd25-review-named.py`, section "WHAT THIS REFUSES TO
CHECK":

> **It cannot tell whether a verdict is REALLY negative.** `GO AT 20 LINES,
> AND A NEW WALL` (`[LJ-1.161]`) is positive and negative at once, and `NOT
> REFUTED, FRAME GREEN` (`[LJ-1.125]`) announces no negative while carrying
> the word. So the table is tunable, the tool explains itself, and a false
> positive is silenced with a reason, never by deleting a word.
>
> **It cannot tell whether the review was any GOOD.** DD25 asks for an
> adversarial review at maximum effort; this checks that one was NAMED. A
> named review that agrees with the negative is a real result and still
> satisfies the gate.
>
> **It cannot fire at the moment the return lands**, which is when the
> orchestrator forgets. The honest enforcement point is the commit or the
> gate, and this tool is that gate: it fires at `make check`, later than the
> forgetting and exactly when the orchestrator is forced to look.
>
> **The vocabulary is not every negative.** A bare `NO` verdict, a `REGRESSED`
> row, a `RED` gate and an `ANSWERED NO` are real negatives that the table
> does not carry, deliberately: `NO` would fire on `NO REPLACEMENT` and `NO
> HYPOTHESIS LEFT`, which are GO rows.
>
> **A declared reason is not a checked reason.** `DD25 review not needed:
> <reason>` is an escape hatch (C-43): the token becomes legal wherever the
> table fires, and a wrong use passes. What the gate delivers is a TRACE an
> audit can find: the row is no longer empty, and the reason is there to
> read.

The same section says a row that IS a DD25 review (the `-R` suffix, or a task
cell naming a DD25, adversarial or Fable-5 review) is exempt, because it is
the review, not a return needing one.

## 3. THE `make check` WIRING

- New target `dd25:` runs `$(PY) scripts/check-dd25-review-named.py`, with a
  comment naming the rule and the measured backlog. `make dd25` exits 0.
  MEASURED.
- `dd25` is added to the `check:` line, after `dd4` and before
  `buildmanifest`. `make -n check` shows the target in the dependency list.
  MEASURED (dry run output).
- `dd25` is added to `.PHONY`.
- The `test:` target gains `$(PY) scripts/tests/test_dd25_review_named.py`
  as its last suite.

`make check` itself was NOT run: the brief forbids it, both Agda slots are
held, and the typecheck target runs Agda.

## 4. THE OTHER GATES, AFTER THE WIRING

- `python3 scripts/check-task-index.py`: `task index OK: 507 cited codes,
  523 unique rows, all within 200 characters`, exit 0. MEASURED.
- `python3 scripts/check-rule-ids.py`: `clean (45 files, 145 lessons, 67
  decisions)`, exit 0. MEASURED.
- `python3 scripts/check-dd4-stated.py`: exit 1, on THREE files, none in my
  write scope: `agents/tasks/LJ-1-200/LJ-1.200-report.md`,
  `LJ-1.201-report.md` and `LJ-1.204-report.md`. **This red is pre-existing,
  not caused by this task.** Evidence: the first two are committed at HEAD
  (`git log` shows `1c87f3a` and `24eaddf`, both before this session), and
  the third is a sibling's modified in-progress report. The checker's brief
  glob `[A-Z]*.md` treats an uppercase-named report as a brief, and none of
  my files match that glob (`lj-1.208-report.md` is lowercase, and my other
  two files are not `.md` under `agents/tasks/`). I touched none of the
  three. INFERRED that this red predates my session from the git evidence;
  MEASURED that my files are not scanned by it.

## 5. THE DESIGN, AND THE LIMITS IT CHOSE

- **The check.** For every task-index row, the VERDICT CELL is read against
  the table. A row that carries a token must (1) name a review code whose own
  row is a DD25 review, (2) declare `DD25 review not needed: <reason>` with a
  non-empty reason, or (3) be in `PRE_EPOCH`. Otherwise it fails.
- **The reason marker requires a word character after the colon.** Measured
  defect in my own first draft: the `|` cell separator satisfied
  `\S+`, so `DD25 review not needed:` at the end of a cell silently passed.
  The regex is now `DD25 review not needed:\s*\w`, and the test pins the
  empty-reason failure. MEASURED.
- **A cited code must BE a review.** A negative row that cites `[LJ-9.8]`
  where `LJ-9.8` is a build row still fails. The review set is derived from
  the index itself: the `-R` suffix, or a task cell naming a DD25,
  adversarial or Fable-5 review. MEASURED (test).
- **PRE_EPOCH is the measured 42**, frozen in the file with the date, and
  `--quiet` suppresses the listing. Nothing is ever added to it.
- **The vocabulary table is the DD4 answer too**: it is the shared table,
  written once, read by this gate and by any later rule that needs "what
  counts as a negative". The gate itself is the mechanical half of DD25's
  own enforcement point; nothing here writes fixed or duplicates a rule.

## 6. CONSTRAINTS MET

- `python3 -m py_compile` after every edit of both Python files; reported at
  each run. MEASURED.
- `python3 scripts/lint-prose.py --check` on this report: see the command
  below; exit 0. MEASURED.
- No em dash anywhere in this report or the checker. MEASURED (linter).
- `Makefile` copied aside to `/tmp/LJ-1.208-Makefile.bak` before editing, per
  the brief's copy-aside rule.
- Report skeleton written in the first five minutes (C-22), filled
  incrementally.
- No Agda, no `dispatch.py`, no edits to `dev/PLAN.md` (a row is the owner's
  under DD0: this gate reports, it never repairs), no edits to
  `.claude/skills/herdr/SKILL.md`, no commit, no push.

## 7. ARCHIVE USED (DD18)

- `scripts/check-dd4-stated.py`, read WHOLE. Took the shape: a narrow gate,
  a docstring that states its own limits (`:13-60`), a frozen `PRE_EPOCH`
  reported never failed (`:72-80`), and a summary that prints the
  grandfather count.
- `scripts/check-task-index.py`, read WHOLE. Took the section anchor
  `### Task index` (`:44`) and the read-from-disk/parse-from-text split
  (`index_rows`, `:94`) that makes the checker testable.
- `scripts/check-rule-ids.py`, read WHOLE. Took `[LJ-1.194]`'s one counting
  path (`duplicate_codes`, `:202`) and the finding that resolution is never
  uniqueness (`duplicate_decisions`, `:228`), which is this task's argument
  in the DD25 shape.
- `agents/tasks/LJ-1-183/lj-1.183-report.md`, read WHOLE. Took F5
  (`:132-140`): the four negative rows named no review, the enforcement
  point was the index row, and the fix the orchestrator announced was
  incomplete. The backlog of 42 is this finding's full extent, swept.
- `dev/PLAN.md:258` (DD0: a row is the owner's; this gate reports, never
  repairs), `:268` (DD17), `:274` (DD25, whose own words say the honest
  enforcement is that the row is empty and visible), `:414` (section 11),
  `:472` (the task index), and the rows `:735-762` for the four controls.
  Read; NOT edited.
- `dev/ORCHESTRATION.md:13-116` (section 1, DD17's switch), `:38-114`
  (section 1.1, DD25's operational form), `:167-377` (section 3, the brief).
  Read; NOT edited.
- `dev/LESSONS.md`, read the entries the brief names whole: D-26 (`:1693`),
  C-31 (`:1873`), I-5 (`:1213`), P-l (`:2323`), C-32 (`:2965`), C-33
  (`:3005`), C-34 (`:3189`), D-29 (`:3260`), C-36 (`:3302`), D-30 (`:3350`),
  C-37 (`:3399`), C-39 (`:3539`), C-40 (`:3620`), C-41 (`:3657`), C-42
  (`:3704`), C-43 (`:3758`). Took C-43 for the escape-hatch paragraph of the
  docstring and C-42 for the sweep: the backlog is the full sweep of the
  negative shape, one level, the index.
- `python3 scripts/rules.py --for build` run and every statement read; the
  build bundle is Agda-master law, and this task writes no Agda, so the
  bundle's content rules do not bind here (stated, not assumed).

## 8. LITERATURE (DD18)

Not this task's subject. None read.

## 9. DD4

**Maximize the code the two proofs share, and write it generic.** This task
writes no proof code. Its DD4 substance is the vocabulary table: written once
as `NEGATIVE_VERDICT`, with a reason per row, so the next rule that needs
"what counts as a negative" imports the table instead of reinventing a regex
inline, and a vocabulary written inline is paid for twice. The gate is one
code path over every row of one series, the same shape `[LJ-1.194]` gave
`check-rule-ids.py` for every series.

## 10. THE FINDINGS THAT MATTER

1. **The backlog is 42 rows**, not four. `[LJ-1.183]` measured four; the
   orchestrator fixed four; the full sweep of the index finds 42 rows whose
   verdict announces a negative and whose row names no review. **9 of the 42
   name no review while a review row naming them exists in the same table**:
   `LJ-1.6` (`LJ-1.6-R`), `LJ-1.17` (`LJ-1.17-R`), `LJ-1.27` (`LJ-1.27-R`),
   `LJ-1.33` (`LJ-1.33-R`), `LJ-1.34` (`LJ-1.34-R`), `LJ-1.38`
   (`LJ-1.38-R`), `LJ-1.185` (`LJ-1.201`), `LJ-1.196` (`LJ-1.200`), and
   `LJ-1.60` inside `LJ-1.129`'s route span. The other 33 rows have no
   review row at all, and most predate DD25's ruling (2026-08-10).
   MEASURED by exact-code scan over the table.
2. **The gate is green from its first run** because the backlog is frozen,
   exactly as `check-dd4-stated.py` freezes its twelve. A negative row
   authored after today that names no review is a defect. MEASURED.
3. **`check-dd4-stated` is red on the tree for three report files outside
   this task's scope** (evidence in section 4). Pre-existing, untouched.
