# LJ-1.212: build the PREMISES gate, `[LJ-1.211]`'s change 1

STATUS: COMPLETE. Written incrementally per C-22. The skeleton existed
before the first measurement finished.

No file outside the write scope was edited. No Agda ran. No dispatch
happened. No commit and no push happened. Every claim is marked MEASURED or
INFERRED.

## 0. LEAD

**The false-positive rate is 23.7 percent, and the gate lands. MEASURED.**

The raw trigger list from `[LJ-1.211]` fires on 118 of 118 live briefs.
That is 100 percent. MEASURED. A list that fires on most briefs is the abort
case the brief names. A gate that fires wrongly trains the author to paste a
heading. So the list is tuned against the record, and the gate lands with a
narrower list. The ACTIVE list fires on 28 of 118 live briefs. That is 23.7
percent. MEASURED.

The gate is built. It refuses a brief that carries an ACTIVE trigger token
and no `## PREMISES` section with a basis at `file:line`. The four tokens
that measured unworkable stay in the table as REFUSED rows. They never fire.
The report shows why each token earns its place.

The three runs:

1. The real tree passes after grandfathering. MEASURED.
2. A synthetic brief with a trigger and no `## PREMISES` fails. MEASURED.
3. The false-positive rate is measured. MEASURED.

## 1. THE FALSE-POSITIVE RATE

The measurement ran the trigger list over every live brief. The census
follows `check-dd4-stated.py`: a file whose name starts with an uppercase
letter, in a live task directory. The count was 118 briefs on 2026-08-14.

The raw list fires on 118 of 118. MEASURED. The three tokens that fire on
every brief are `section`, a LESSONS law ID, and, at 83.9 percent, a figure
with any unit. The narrow forms tell the story:

| trigger token | fire rate | verdict |
|---|---:|---|
| the gate is | 3 of 118, 2.5 percent | ACTIVE |
| GO needs | 1 of 118, 0.8 percent | ACTIVE |
| NO-GO is | 3 of 118, 2.5 percent | ACTIVE |
| the only lever | 0 of 118, 0.0 percent | ACTIVE |
| shapes | 9 of 118, 7.6 percent | ACTIVE |
| measure it, do not argue it | 0 of 118 live, 0.0 percent | ACTIVE |
| a figure with a unit, threshold form | 16 of 118, 13.6 percent | ACTIVE |
| a figure with a unit, bare form | 80 of 118, 67.8 percent | REFUSED |
| section plus a number | 54 of 118, 45.8 percent | REFUSED |
| a LESSONS law ID | 118 of 118, 100 percent | REFUSED |
| do not weaken | 40 of 118, 33.9 percent | REFUSED |

The ACTIVE union fires on 28 of 118 live briefs. That is 23.7 percent.
MEASURED. The REFUSED tokens measured unworkable. A REFUSED token is not a
judgment on its shape. It is a measured count: the token fires on most or
many briefs, so a red gate on it would buy a pasted heading.

The tree grew while the gate was wired. `[LJ-1.213]`'s and `[LJ-1.214]`'s
briefs landed mid-run. Each carries no ACTIVE trigger, so each passes. The
gate stays green as the count moves from 118 to 120, with the same 28
frozen. MEASURED.

## 2. THE THREE RUNS

**Run 1, the real tree. MEASURED.**

```text
$ .venv/bin/python scripts/check-premises-stated.py
check-premises-stated: 118 briefs, 28 frozen pre-epoch brief(s) with a
trigger and no declared premises, 0 new defects
```

Exit status 0. Re-run after `[LJ-1.213]` landed: 119 briefs, 28 frozen,
0 new defects, exit 0. MEASURED.

**Run 2, the synthetic brief. MEASURED.**

```text
$ .venv/bin/python scripts/check-premises-stated.py --tasks <fixture>/tasks
check-premises-stated: 1 brief(s) carry a trigger and no declared premises,
0 frozen pre-epoch:
  .../LJ-9.99.md: carries no ## PREMISES section; carries: NO-GO is

A brief that funds a gate, a build or a probe on a premise declares that
premise in a `## PREMISES` section.
Write the section, one premise per line, each with a basis at `file:line`:
  ## PREMISES
  - <the premise> at <file:line>
The return marks each premise VERIFIED or REFUTED at `file:line`.
```

Exit status 1. The message names the token and shows the section shape in
one read. The test suite pins this and 21 more checks.

**Run 3, the false-positive rate. MEASURED.**

The raw list fires on 118 of 118. The ACTIVE list fires on 28 of 118. The
per-token counts are in section 1. The gate lands because the ACTIVE rate
is 23.7 percent, not most.

## 3. THE TRIGGER TABLE AS TUNED

The table lives in the checker as a module constant, `TRIGGER`, at
`scripts/check-premises-stated.py:163`. Each row is a token, a match mode,
an ACTIVE flag, and the reason it earns its place. `[LJ-1.211]` names every
token, and every ACTIVE token has a measured overturn brief behind it.

| token | mode | earned by |
|---|---|---|
| the gate is | phrase | LJ-1.7-R: its brief shipped the conclusion as a heading, `THE GATE IS OPEN AND I MEASURED IT MYSELF` (`agents/tasks/archive/LJ-1-7/LJ-1.7.md:15`) |
| GO needs | phrase | LJ-1.15-R: its brief fixed the gate as `GO needs BOTH` (`agents/tasks/archive/LJ-1-15/LJ-1.15.md:45`) |
| NO-GO is | phrase | LJ-1.15-R: its brief fixed the gate as `NO-GO is` (`agents/tasks/archive/LJ-1-15/LJ-1.15.md:47`) |
| the only lever | phrase | `[LJ-1.211]` names it. One lever is a load-bearing claim by construction. No live brief carries it. |
| shapes | word | LJ-1.16-R and LJ-1.33-R: their briefs named shapes (`agents/tasks/archive/LJ-1-16/LJ-1.16.md:40`) |
| measure it, do not argue it | phrase | LJ-1.34-R and LJ-1.50: their briefs carried it (`agents/tasks/archive/LJ-1-34/LJ-1.34.md:86`, `LJ-1.50.md:54`). C-34 measures its cost. |
| a figure with a unit | threshold | LJ-1.15-R (`40 lines or fewer`) and LJ-1.66-R (`under 0.05 s`). These are the two reviews that wrote the cure. |

The threshold form is the tuning. It matches a figure with a unit and a
comparator: `or fewer`, `or more`, `at least`, `under`, `over`. That is the
shape a fixed gate writes. The bare form, a figure with any unit anywhere,
fires on 67.8 percent and is REFUSED.

The REFUSED rows, and where their cures live:

| token | fire rate | the cure |
|---|---:|---|
| a figure with a unit, bare form | 80 of 118, 67.8 percent | the threshold form keeps the measured gate shape |
| section plus a number | 54 of 118, 45.8 percent | C-32: cite whole documents, never a section (`dev/LESSONS.md:2965-3004`) |
| a LESSONS law ID | 118 of 118, 100 percent | `[LJ-1.211]`'s change 3: a law citation quotes the law's action |
| do not weaken | 40 of 118, 33.9 percent | C-36: write both halves, do not weaken AND you MAY strengthen (`dev/LESSONS.md:3302-3350`) |

The REFUSED rows still earn their place in the table. The measured count is
the reason they cannot gate. DD4 binds the table: a third rule that needs
premise-trigger or negative-verdict vocabulary reads the table, and never
reinvents a regex inside a function.

The ACTIVE gate catches the briefs of 6 of the 8 brief-caused overturns.
MEASURED: LJ-1.15, LJ-1.16, LJ-1.33, LJ-1.50, LJ-1.7 and LJ-1.66 all carry
an ACTIVE token. The two it misses, LJ-1.32 and LJ-1.17, carry only REFUSED
shapes: a section-scoped read and a bare figure. Each is already a named
law with its own cure, C-32 and C-31. That is the honest boundary of the
gate, and it is the price of the 23.7 percent rate.

## 4. THE BACKLOG

The backlog is 28 of 118 live briefs. MEASURED 2026-08-14. That number is
the honest scale of the lapse: 28 briefs carry an ACTIVE trigger and none
declares its premises.

The set is frozen in `PRE_EPOCH` at `scripts/check-premises-stated.py:196`.
It is reported once and never fails. Nothing is ever added to it. A new
brief that fires is a defect.

The set includes `LJ-1-212`, the gate's own brief. It was written before
the gate existed, and the task's write scope forbids editing it. The set
also includes three uppercase report files, `LJ-1.200-report.md`,
`LJ-1.201-report.md` and `LJ-1.204-report.md`, because the census follows
the `[A-Z]*.md` glob that `check-dd4-stated.py` uses.

## 5. WHAT THE GATE CANNOT SEE

Quoted from the docstring at `scripts/check-premises-stated.py:47`:

- "It cannot tell whether a premise is TRUE. It checks that the author
  listed one and gave it a basis."
- "It cannot tell whether the basis at `file:line` says what the author
  claims. Write the basis so a review can read it."
- "It cannot fire at the moment the brief is WRITTEN, which is when the
  failure happens. It fires at the commit or the gate."
- "It reads the brief, never the return. The return's VERIFIED and REFUTED
  marks are not checked."

The section check is mechanical, so the third abort case does not fire. A
`file:line` basis has a distinctive shape: a filename, a colon, a line
number. The gate requires the heading and one such shape under it. It never
judges the premise or the basis. The docstring says so, because `AGENTS.md`
says a row claiming more than its checker delivers is false safety.

## 6. THE MAKE CHECK WIRING

The `premises` target is wired into `make check` beside `dd25`, at
`Makefile:18`. Its target runs the checker at `Makefile:172`. The comment
above the target states the measured rates and the limits.

Verified: `make premises` exits 0. MEASURED. `make check` itself was not
run, as the brief orders.

## 7. ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-211/lj-1.211-report.md`, read WHOLE. TOOK the cause
  split, change 1's mechanism and trigger list, and the two source reviews.
- `scripts/check-dd25-review-named.py`, read WHOLE. TOOK the gate shape,
  the PRE_EPOCH pattern, and the docstring that states its own limits.
- `scripts/check-dd4-stated.py`, read WHOLE. TOOK the epoch pattern and the
  briefs() census.
- `scripts/check-archive-cited.py`, read WHOLE. TOOK the REPORT shape,
  considered it, and did not take it: the ACTIVE rate is low enough to gate.
- `scripts/tests/test_dd25_review_named.py`, read WHOLE. TOOK the test
  shape.
- `agents/tasks/archive/LJ-1-66/lj-1.66-review.md:230-258`, read. TOOK the
  two-part gate: cost term AND structural premise, verified before building.
- `agents/tasks/archive/LJ-1-15/lj-1.15-review.md:407-409`, read. TOOK the
  line-gate derivation cure.
- The archived briefs at their token lines: `LJ-1.7.md:15`, `LJ-1.15.md:45-51`,
  `LJ-1.16.md:40`, `LJ-1.17.md:19-35`, `LJ-1.32.md:101-104,132`,
  `LJ-1.34.md:86`, `LJ-1.41.md:188`, `LJ-1.50.md:54`, `LJ-1.66.md:92-95`.
  Each names the shape that earns or refuses its token.
- `dev/LESSONS.md`: C-31 at 1873-1913, C-32 at 2965-3004, C-33 at
  3005-3054, C-34 at 3189-3217, C-36 at 3302-3350, C-37 at 3399-3444,
  C-39 at 3539, C-40 at 3620, C-42 at 3704, C-43 at 3758, D-26 at 1693,
  D-29 at 3260, D-30 at 3350, I-5 at 1213. TOOK the actions the gate's
  docstring must state.
- `dev/PLAN.md:258`, the DD0 row. TOOK the standing prohibition: no DD row
  was edited.

## 8. LITERATURE USED (DD18)

Not this task's subject. None read.

## 9. CRAFT EVIDENCE

- C-22. The report skeleton was created before the first measurement
  finished, and filled as answers landed. MEASURED.
- The checker stays valid Python. `.venv/bin/python -m py_compile
  scripts/check-premises-stated.py scripts/tests/test_premises_stated.py`
  passes after every edit. MEASURED.
- The test suite passes. `.venv/bin/python
  scripts/tests/test_premises_stated.py` exits 0 with 22 checks. MEASURED.
- The report passes the prose lint. See the constraint run below. MEASURED.
