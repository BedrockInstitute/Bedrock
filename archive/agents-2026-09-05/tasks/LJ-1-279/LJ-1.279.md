# LJ-1.279: LAND A5 rows 5 and 1 as `src/L/InjChain.lagda.md`

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **I ran `scripts/dispatch_policy.py` before writing this
line**: `deepseek-subagent-mode` is IN FORCE, clock-selected, OFF-PEAK, Beijing
window 12:00 to 14:00.

## GOAL

**Land Route A-prime's A5 rows 5 and 1 as ONE new master,
`src/L/InjChain.lagda.md`.**

**`[LJ-1.268]` put both there** (`agents/tasks/LJ-1-268/lj-1.268-report.md:26`
and `:31`). **Row 5 is independent and lands in wave 0. Row 1 needs A2, which
LANDED TODAY** as `src/L/Coding/Injection.lagda.md`, green, with a re-run that
imports it exiting 0. **So both rows are open in one pass.**

**A5 is one block whose rows split across three waves.** **Rows 2 and 4
DISSOLVED**, measured by `[LJ-1.247]`. **Row 3 is NOT yours**: it is blocked on
a stale probe import and lands in wave 3.

## PREMISES

- **Row 1 is 160 lines and it is NEEDED**, measured by `[LJ-1.264]` at
  `agents/tasks/LJ-1-264/lj-1.264-report.md:1`. **Its own finding is that
  `noinj-squared` survives at a second site the two dissolutions never
  touched.** **If row 1 turns out NOT to be needed, that is a dissolution and
  it is worth more than the landing.**
- **Row 5 is delivered as a green probe** at
  `agents/tasks/LJ-1-234/ProbeLJ1234A.agda:1`, and `[LJ-1.268]` records it as
  wave 0 with every import delivered
  (`agents/tasks/LJ-1-268/lj-1.268-report.md:26`).
- **Row 1's only undelivered import was A2**, per
  `agents/tasks/LJ-1-268/lj-1.268-report.md:31`. **VERIFY THIS FIRST** against
  the landed `src/L/Coding/Injection.lagda.md`. **A2's master exports less than
  its probe did, because `[LJ-1.277]` made a P-k boundary decision and kept the
  readback private.** **If row 1 needs something A2 kept private, say so: that
  is a real finding about the boundary and I re-open it rather than you.**
- **Rows 2 and 4 dissolved**, measured at
  `agents/tasks/LJ-1-247/lj-1.247-report.md:1`. **Do not rebuild them.**
- **The prices are in the NARROW caliber.** `[LJ-1.277]` measured A2 delivering
  238 against a priced 186, ratio 1.28, because
  `agents/tasks/LJ-1-229/lj-1.229-report.md:17` counts definitions only while
  DD5 counts non-blank lines inside fences. **Expect more than 160 plus row 5
  and say what you get.**

## THE SOURCES

| row | probe | note |
|---|---|---|
| row 5, `pairω` | `agents/tasks/LJ-1-234/ProbeLJ1234A.agda` | independent, wave 0 |
| row 1, the composition of two injections | `agents/tasks/LJ-1-264/ProbeLJ1264A.agda` | 160 lines, needs A2 |

**Read both whole before you write anything.** **Take their content, not their
names.**

## WHAT YOU DECIDE, and say why in the report

**1. THE ORDER INSIDE THE FILE, and what each row exports.** **P-k: a read
lemma is stated where its consumers use it.** **A6 and A7 are downstream; name
what each needs.** **Row 3 lands here later, in wave 3: leave it a place and
say where.**

**2. WHAT `src/Everything.lagda.md` NEEDS.** **NEVER touch that file. I wire
it.** **Name the exact line and its position, derived from the master's own
imports and its consumers.**

## THE MEASUREMENT YOU OWE

**The delivered master's cold elapsed time, its line count by
`.venv/bin/python scripts/ledger.py`, and its rate against the 0.010514 bar.**
**A2 landed at 0.0070 s/line, 0.66x the bar, in the P-m parameterized class.**
**Say whether this master is in the same class and why.**

**And name every existing master you did NOT edit.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **BOTH ROWS LAND GREEN.** Report the exports, the `Everything` line, the
  timing, the rate and the delivered size. STOP.
- **ROW 1 NEEDS SOMETHING A2 KEPT PRIVATE.** **Name it at `file:line` and
  STOP.** **Do not edit A2.** **That is a boundary decision and it is mine to
  re-open.**
- **ROW 1 IS NOT NEEDED.** **That is a dissolution, the sixth this month, and
  it is worth more than the landing.** **Give the evidence and stop.**
- **AN IMPORT IS NOT DELIVERED.** **Name it at `file:line`** (C-44).
- **A WALL.** **A single `agda` invocation past 30 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **Report a heap exhaustion as
  a wall. NEVER raise the cap.**

## WHAT YOU MUST NOT DO

- **NEVER touch `src/Everything.lagda.md`.** I wire it after auditing.
- **Do not edit ANY existing master**, including today's
  `src/L/Coding/Injection.lagda.md` and `src/L/Coding/EnvSupply.lagda.md`.
- **Do not land A5 row 3, A6 or A7.** **Row 3 is blocked on a stale import and
  lands in wave 3.**
- **Do not rebuild A5 rows 2 or 4.** **They dissolved.**
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **Do not touch `agents/tasks/LJ-1-278/`.** **A SIBLING IS LIVE THERE**,
  landing A1, A3 and A4 into `src/L/Cardinal.lagda.md`. **Your write territory
  is `src/L/InjChain.lagda.md` and `agents/tasks/LJ-1-279/`, and nothing else
  under `src/`.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the load beside every absolute figure.**
- **Create your report file in your FIRST five minutes (C-22).**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE RULES THIS CHAIN EARNED

**`exit 0` IS NOT A SUPPLY** (C-45). **`[LJ-1.263]` and `[LJ-1.277]` both
proved a landing by re-running something that IMPORTS the new master.** **Do
the same.**

**C-40. A new master has consumers the moment it exists.**

**C-49.** **A heap wall and a rate can be properties of the LAYOUT rather than
the content.**

**C-44. A brief's claim is unchecked until you check it.**

**THE CALIBER IS DD5'S AND NOTHING ELSE.** **`scripts/ledger.py` is the only
admissible source for a size figure.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.248]` measured A-prime's per-tower half at 146 to 196 lines, a BAND
because the partition is a survey and it EXCLUDES A5.** **So A5's tower status
is the gap in that measurement, and you are the first to land any of it.**
**Say, for each row, whether it is per-tower or tower-neutral, and give the
evidence.**

**NAME YOUR AXIS** (C-46). **`[LJ-1.272]` measured that DD4's OWN axis is
AC-against-GCH, fixed in code at `scripts/ledger.py:50`, and that 12 of 62 DD4
figures in this phase name no axis at all.** **Do not be the thirteenth.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-234/ProbeLJ1234A.agda` and
  `agents/tasks/LJ-1-264/ProbeLJ1264A.agda`, both read WHOLE.**
- **`agents/tasks/LJ-1-264/lj-1.264-report.md`**: why row 1 is needed and where
  `noinj-squared` survives.
- **`agents/tasks/LJ-1-247/lj-1.247-report.md`**: rows 2 and 4 dissolving, and
  the three greps that found the column square in NO `src/` file.
- **`agents/tasks/LJ-1-268/lj-1.268-report.md:23-48`**: the landing order.
- **`agents/tasks/LJ-1-277/lj-1.277-report.md`**: **how A2 was landed and
  PROVED today, and the P-k boundary it chose.** **Copy the method and check
  the boundary.**
- **`archive/dev/TASKS-archived.md`.** **The retired route built injection
  chains too. Take SHAPE from the archive, never a claim**, and say what would
  NOT transfer.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md` splits II.5 into twelve rows.** **Say which
rows A5's two rows serve**, and whether the literature says anything about
composing injections at all. Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-264/ProbeLJ1264A.agda` FIRST, whole.

## SCOPE (write)

`src/L/InjChain.lagda.md`, new, and `agents/tasks/LJ-1-279/` for your report
and any working file. **No existing master. Never `src/Everything.lagda.md`.**
**Do not create any other file under `src/`.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for build` and read every statement.
**The tool prints `Full entry: dev/LESSONS.md:<line>` for every rule and says
THIS IS AN EXCERPT when it truncated. OPEN the full entry for any law you act
on.**

- **P-h.** Definability walks are module-parameterized, never
  function-parameterized.
- **P-k.** A read lemma is stated where its consumers use it. **The centre of
  your ordering decision.**
- **P-l.** A statement may be ABOUT a concrete stage without dragging that
  stage's presentation into its type.
- **P-m.** The check-cost rate is a content-class certificate.
- **P-n.** Satisfaction content at a concrete carrier is a payable floor.
- **R-35.** Union representations are meta-poisoned.
- **R-38.** A consumer's alias of a transparent imported operation is a birth
  site.
- **R-40.** A deep successor-chain membership witness normalizes
  super-linearly.
- **I-5.** Inner-world truncation branches carry written types.
- **C-12.** Agda runs under a hard heap cap.
- **D-10.** Price the truth of a recorded residue before pricing its proof.
- **C-22.** Write your deliverable incrementally.
- **C-32, C-36, C-40, C-44, C-45, C-46, C-49. D-1, D-26. DD0, DD8, DD23,
  DD24.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `.venv/bin/python scripts/lint-prose.py --check` and
  `.venv/bin/python scripts/lint-agda.py --check` on what you write.
- **`lint-agda.py` binds a MASTER and did not bind the probes.** **Expect to
  trim the using lists; A2's landing removed many.**
- **DD23 freezes mathematical prose.** **Write code and its own comments only.**
- **No em dash in any language.** Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with the delivered line count, the cold elapsed seconds and the rate
against 0.010514.** Then each premise above marked VERIFIED or REFUTED at
`file:line`. Then what the master exports, per row, with its consumer, and
where row 3 will go. Then the exact `src/Everything.lagda.md` line. Then the
re-run that PROVES this is a landing. Then every existing master you did not
edit. Then the DD4 answer, per row, with its axis. **Mark every negative
MEASURED or INFERRED.**
