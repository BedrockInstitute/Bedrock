# LJ-1.367: give the DD24 bar ONE home, and gate every restatement of it

tier: pi (pi-subagent-mode), model `glm-5.3`. **I ran
`scripts/dispatch/dispatch_policy.py` before writing this line and took the
head it gave.** No Agda. **BUILD.**

## THE OWNER'S INSTRUCTION, in their own words

> **Sort out the consistency of the documents and the script comments
> properly. Do not write one thing here and another thing there, drifting
> here and pinned there. Do it all at once now, and do not make this mistake
> again.**

**「Do not make this mistake again」is the load-bearing half.** **A one-time
tidy that nothing enforces will decay, and this project has measured that
twice this week.** **So the deliverable is HALF sweep and HALF gate, and the
gate is the part that matters.**

## WHAT HAPPENED, because the sweep is meaningless without it

**DD24's bar is seconds per line. It had FOUR homes and it drifted.**

- **The owner's rule was already recorded** at `dev/ledger.toml:2783`: 「the AC
  side was FIXED when its trophy landed and nothing written afterwards joins
  it」.
- **It was implemented as a MEMBERSHIP guard only.** The Landmarks cone gains
  no members, MEASURED. **Nothing stopped the SECONDS being re-timed.**
- **On 2026-08-13 a recalibration on a tree cured by `[LJ-1.147]`'s seal moved
  the bar from 0.013602 to 0.010514, about 13 percent tighter.** **It stayed
  moved for three days.** `[LJ-1.364]` found it on 2026-08-16 while ruling a
  different question, and the owner reversed it.
- **DD19 already forbade this**: one home per rule, nothing canonical twice,
  and a rule no machine enforces must NAME its enforcement point. **The bar
  had no enforcement point and four restatements.**

## THE DESIGN, and it is MINE. Implement it; do not redesign it.

**TWO HOMES, and each holds a different KIND of thing.**

1. **THE NUMBERS live in `dev/ledger.toml`'s `[ratio]` table, and nowhere
   else.** The applied bar is `ac_baseline_module_rate` times `tolerance`,
   computed at `scripts/measure/check-ratio.py`. **I have already restored
   `ac_baseline_module_rate` to 0.011828 over 17,185 lines, so the bar is
   0.013602. Verify that; do not change it.**
2. **THE RULE lives in `dev/PLAN.md`'s DD24 row, and it now STATES NO
   FIGURE, by design.** **I have already rewritten it. Read it and make
   everything else consistent WITH it.**

**Everything else NAMES THE FIELD and never the value.**

## THE THREE CLASSES, and the whole job is telling them apart

**This is the part a careless sweep gets wrong, so it is stated first.**

- **A LIVE CLAIM**: text asserting what the bar IS today. **These must be
  converted to name `ac_baseline_module_rate` and `tolerance`, or the ledger
  table, instead of a number.**
- **A HISTORICAL MEASUREMENT in a dated record**: a lesson, a task-index row,
  a journal entry. **A RECORD IS NEVER REWRITTEN.** **These KEEP their
  figures and gain a marker saying the figure is historical and naming its
  date.** **Do not delete a measurement to make a checker green; that is the
  failure mode this task exists to prevent, one level up.**
- **A TEST**: `scripts/tests/test_ratio_noise.py:172` restates the
  arithmetic in a comment. **A test may hold a figure only if it READS it
  from the ledger, or if the comment names the field it tracks.** **Choose
  and say which.**

## THE SWEEP, and these are the sites I MEASURED. Find the ones I missed.

```
0.010514  dev/ledger.toml  dev/PLAN.md
0.013602  dev/ledger.toml  dev/PLAN.md  scripts/tests/test_ratio_noise.py
0.009143  dev/ledger.toml  dev/PLAN.md  dev/LESSONS.md
0.011828  dev/ledger.toml  dev/PLAN.md  dev/LESSONS.md  scripts/tests/test_ratio_noise.py
0.013193  dev/ledger.toml  dev/PLAN.md  dev/LESSONS.md
0.011472  dev/ledger.toml
0.008793  dev/ledger.toml
```

**Known live claims now STALE, all in `dev/PLAN.md`:**

- **`:145`** and **`:212`**: status prose quoting the 0.010514 bar. **Both are
  wrong today.**
- **`:1271`**, `[LJ-1.265]`'s task-index row: reads 「0.010514 IS LIVE」 and
  「0.013193 is STALE」. **THAT IS A RECORD OF WHAT A DISPATCH FOUND AND IT IS
  NOT REWRITTEN.** **DD19's own pattern applies: a revision is RECORDED
  rather than a row being rewritten.** **So add a superseding row, do not
  edit that one.** **I have registered `LJ-1.366` for the owner's reversal;
  use it as the superseding code.**

**Known historical measurements in `dev/LESSONS.md`:**

- **`:3027`**: 「Neither cure alone passes DD24's 0.013193 bar」. **The
  measurement stands; the phrase「DD24's … bar」asserts a live threshold.
  Mark it.**
- **`:3839`**, P-y: records `ac_baseline_module_rate` falling 0.011828 to
  0.009143. **THIS IS THE MEASUREMENT THAT CAUSED THE DRIFT AND IT MUST
  SURVIVE INTACT.** **Add that the owner reversed the re-basing on
  2026-08-16 and the fall is a fact about a later tree, not about the bar.**

**`scripts/measure/check-ratio.py`**: read its comments whole and make every
statement about which figure is authoritative agree with the two homes.
**`:468-478` already says the header must advertise the bar actually applied;
check that it still does.**

## THE GATE, which is the deliverable that outlives the sweep

**`scripts/gate/check-baseline-home.py`, wired into `make check`.**

**It refuses a bar figure stated as a LIVE threshold outside
`dev/ledger.toml`'s `[ratio]` table.**

**How it can tell the classes apart is your design problem, and the honest
answer may be a marker rather than a heuristic.** **A workable shape: any
occurrence of a `[ratio]` figure outside the ledger must sit on a line
carrying an explicit historical marker you define, or inside a file you
declare as reading the ledger.** **State the marker's spelling in the
checker's docstring so an author can comply without guessing.**

**It must also catch the NEXT figure, not only today's seven.** **Read the
`[ratio]` table and derive the literals; do not hardcode them.** **A checker
that hardcodes the numbers it guards has the drift it is preventing.**

**AN EPOCH IS REQUIRED.** **`check-dd4-stated.py`'s `PRE_EPOCH` and today's
`SECOND_EPOCH` in `check-premises-stated.py` are the worked examples.** **A
gate that fails the whole corpus teaches authors to paste.** **Write the
frozen scale into the code's comment, never into a commit message** (C-59).

## THE ABORT CRITERION (D-1)

- **THE SWEEP LANDS AND THE GATE IS GREEN.** Report every site changed, every
  site left alone with its reason, and the gate's runtime. **Best.**
- **THE CLASSES CANNOT BE TOLD APART MECHANICALLY.** **Then say so and gate
  only what can be: for instance, the live-status files but not
  `dev/LESSONS.md`.** **A narrower gate that is honest beats a wide one that
  forces authors to mangle records.**
- **A FIGURE I LISTED IS NOT WHAT I SAY IT IS.** **Say so.** I derived the
  table above with one grep and I did not read every hit in context.

## CONSTRAINTS

- **You MAY edit `dev/LESSONS.md`, `scripts/measure/check-ratio.py`,
  `scripts/tests/test_ratio_noise.py`, create
  `scripts/gate/check-baseline-home.py`, and add ONE `Makefile` target.**
- **`dev/PLAN.md`: you MAY fix the two stale status lines at `:145` and
  `:212`.** **Do NOT touch the DD24 row and do NOT touch any task-index row;
  those are mine.** **Give me the superseding row's text in your report and I
  will add it.**
- **`dev/ledger.toml`: do NOT change any figure.** **You may edit its
  COMMENTS for consistency, and you should.**
- **`src/` is forbidden** (I-5). **`AGENTS.md` is DD19-gated: do not edit it.
  If it needs a line, write the diff into your report.**
- **`[LJ-1.362]` and `[LJ-1.365]` are live and hold both Agda slots, writing
  `src/FOL/Bernstein.lagda.md` and `agents/tasks/LJ-1-365/`.** **Stay out of
  `src/` and you cannot collide.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **Do not run `make check` on the whole
  tree; run YOUR target alone, and read its exit with NO PIPE** (C-59).
- **Do NOT run `check-ratio.py` itself.** It costs minutes and is outside
  `make check` for that reason.
- **Create `agents/tasks/LJ-1-367/lj-1.367-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check`. **No em dash.**
  ASD-STE100. Evidence is `file:line`. Mark every negative **MEASURED** or
  **INFERRED**.

## PREMISES

> **ADDED 2026-08-16 AFTER THE RETURN, AND THE AGENT NEVER SAW THIS SECTION.**
> `check-premises-stated.py` refused this brief, correctly: it carries a
> trigger and no `## PREMISES` heading. **The substance WAS in the brief**, in
> 「THE PREMISE OF MINE MOST LIKELY TO BE WRONG」above, and the return answered
> it. **The form was not, and the gate reads the form.** This section records
> the premise and its verdict so the record is complete; it does not pretend
> the agent read it. **The orchestrator wrote this brief and broke the gate
> the same day it wrote law C-59 about gates going unread.**

- **The bar's numbers already live in `dev/ledger.toml` and nowhere else that matters**, from seven literals I grepped, at `dev/ledger.toml:2599`.
  **REFUTED as incomplete**: the whole-ledger derivation guards **22** figures, and `dev/PLAN.md:502` carried a LIVE claim quoting the superseded 0.007913 of 2026-08-10 against the ledger's 0.008793 since 2026-08-13.
- **`0.013193` is inside the `[ratio]` table**, assumed and never checked.
  **REFUTED**: it lives at `dev/ledger.toml:308`, OUTSIDE `[ratio]`, so a table-only gate would have missed it.
- **The three classes (live, historical, test) can be told apart mechanically**, at `dev/PLAN.md`'s DD24 row.
  **VERIFIED under a marker**: `HISTORICAL(YYYY-MM-DD)` on the figure's own line, `scripts/gate/check-baseline-home.py`, exit 0.

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Eleven of my last thirty-four briefs carried a claim an agent measured
FALSE, and TODAY `[LJ-1.364]` measured two of my claims false in one
return.** **The one at risk: 「the bar's numbers already live in
`dev/ledger.toml` and nowhere else that matters」.** **I grepped seven
literals. I did NOT grep for the bar stated as arithmetic (「0.011828 times
1.15」), as a ratio (「1.56x」,「1.91x」), or in words.** **Those are
restatements too and they drift the same way.** **Sweep for them.**

## THE RULES

**DD19 is the rule this task enforces: one home per rule, nothing canonical
twice, and a rule no machine enforces must NAME its enforcement point.**
**C-59, written today: a gate you do not run is worth what a gate you do not
have is worth; never read a pipe's exit for a gate.** **C-48: a policy that
only a document states is not enforced.** **C-28: a stale figure reports
exactly like a live one, which is why this drift was invisible.**
**C-45, C-57, D-10, C-42, C-44, C-53, P-l, P-k.**
**C-22, C-32, C-36, C-39, C-40.** I-5. **D-1, D-26.**
**DD0, DD4, DD8, DD18, DD19, DD23, DD24, DD25.**

Run `.venv/bin/python scripts/dispatch/rules.py --for build` and
`--grep baseline`, and read every statement.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker. **NAME YOUR AXIS** (C-46).

**Your axis is not the two towers, and you should say so plainly rather than
force the section.** **What IS live: DD24's bar is the instrument that judges
the GCH wing against the AC wing, so a drifted bar mis-reports the DD4
relationship itself.** **The drift made the wing look 13 percent worse than
the ruling allows, for three days, and every verdict quoting it is stale.**
**Say in one line whether any figure you touch is one a DD4 judgement rests
on, so I know what to re-check.**

## ARCHIVE (DD18)

**A live `agents/tasks/` path is NOT an archive citation** and
**`scripts/gate/check-dd18-survey.py` now GATES your return**: name each of
the four corpora, cited or declined in ONE line, and QUOTE one line per
archived file you read, at its real line number.

- **`archive/dev/DECISIONS-archived.md`**: **did the retired route have a
  baseline or a quality bar, and did IT drift?** **A rule that already died
  once is the strongest evidence a gate can carry.**
- **`archive/dev/JOURNAL-archived.md`**: the retired route's own measurement
  episodes. **WHY NOT in one line if nothing bears.**
- **`archive/dev/TASKS-archived.md`**: **grep for a baseline re-measurement.**
- **`archive/src/2026-08-09-rud-route/`**: **almost certainly nothing bears on
  a checker for figures. Say so in one line naming what you checked.**

## LITERATURE (DD18)

**Run `ls dev/literature/` and say in ONE line whether anything bears on
threshold or baseline design.** **`[LJ-1.356]` and `[LJ-1.357]` both measured
that nothing there bears on process mechanisms; cite that and move on.**
Return a **LITERATURE USED** section.

## SCOPE (read)

`dev/PLAN.md`'s DD24 row as I rewrote it TODAY, FIRST. It is the rule the
whole sweep must agree with. Then `dev/ledger.toml`'s `[ratio]` table whole.

## SCOPE (write)

`dev/LESSONS.md`, `dev/PLAN.md` lines `:145` and `:212` only,
`dev/ledger.toml` comments only, `scripts/measure/check-ratio.py`,
`scripts/tests/test_ratio_noise.py`, `scripts/gate/check-baseline-home.py`,
one `Makefile` target, and `agents/tasks/LJ-1-367/`.

## RETURN

**Lead with ONE line: is the bar stated in exactly one place now, and does
the gate hold it there.** Then every site, classed as LIVE, HISTORICAL or
TEST, with what you did to each. Then the sites I missed, including the
arithmetic and ratio spellings. Then the gate's marker spelling, its epoch and
its runtime. Then the superseding task-index row's text for me to add. Then
your own false negatives. **Mark every negative MEASURED or INFERRED.**
