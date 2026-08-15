# LJ-1.277: LAND A2, the coding injection, as `src/L/Coding/Injection.lagda.md`

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **I ran `scripts/dispatch_policy.py` before writing this
line**: `deepseek-subagent-mode` is IN FORCE, clock-selected, OFF-PEAK, Beijing
window 12:00 to 14:00.

## GOAL

**Land Route A-prime's block A2 as a NEW MASTER, `src/L/Coding/Injection.lagda.md`.**
**This is a LANDING, not a probe. The deliverable is a green master in `src/`.**

**Route A-prime is priced at 1,089 lines and NOT ONE LINE IS IN `src/`.** A2 is
wave 0 and it is the block every other block names.

**Why A2 first, in `[LJ-1.268]`'s own words at
`agents/tasks/LJ-1-268/lj-1.268-report.md:23-24`:** it lands in a NEW master,
every import is delivered, and A3, A4, A5 row 1 and A6 all wait on it.

**And it is now on the critical path for something larger.** `[LJ-1.274]`
measured that `dev/ledger.toml`'s `gch_root` needs only a committed
`.lagda.md` under `src/` with an import closure, never a proof term
(`scripts/ledger.py:404-446`). **A2, A4 and A7 are 262 lines, and that is the
day DD4's own report starts working for the first time in this project.**
**A2 is the first of the three.**

## THE SOURCE

**`agents/tasks/LJ-1-229/ProbeLJ1229A.agda` is the green probe, 186 lines.**
Its own header names four sections: `injAt` with out and in; `Extract`, the
readback; `rangeGraph` and `Range`; and `inRanAt` with `ranAt`.

**Read it whole before you write anything.** **Take its content, not its
name.**

## WHAT YOU DECIDE, and say why in the report

**1. WHAT THE MASTER EXPORTS, and what it keeps private.** **The probe's own
header separates the description plus adequacy, which A4 consumes, from the
readback, which A4 does NOT.** **P-k: a read lemma is stated where its
consumers use it.** **So say what A3, A4, A5 row 1 and A6 each need, and put
the boundary there.**

**2. WHAT `src/Everything.lagda.md` NEEDS.** **NEVER touch that file. I wire
it.** **Name the exact line and where in the reading order.**

## THE MEASUREMENT YOU OWE

**The delivered master's cold elapsed time, its line count, and its rate
against the 0.010514 bar.** **The wing's gap is 60.0 s and every landing either
helps or hurts it.** **`[LJ-1.268]` measured that this is a NEW master, so no
over-the-bar master gains a line; verify that claim by naming every existing
master you did NOT edit.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **IT LANDS GREEN.** Report the exports, the `Everything` line, the timing and
  the rate. STOP.
- **AN IMPORT IS NOT DELIVERED.** **`[LJ-1.268]` measured that every A2 import
  is delivered. If one is not, name it at `file:line`** (C-44). **That is a
  refutation of the landing order and it is worth more than the landing.**
- **IT DOES NOT TYPECHECK AS A MASTER.** **The probe is green as `.agda`. If a
  MASTER refuses what the probe accepted, name the difference** (C-36).
  **`lint-agda.py` binds a master and did not bind the probe: expect the
  using-list discipline and import necessity to bite.**
- **A WALL.** **A single `agda` invocation past 30 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **Report a heap exhaustion as
  a wall. NEVER raise the cap.**

## WHAT YOU MUST NOT DO

- **NEVER touch `src/Everything.lagda.md`.** I wire it after auditing.
- **Do not edit ANY existing master.** **`[LJ-1.268]`'s whole landing order
  rests on no existing master gaining a line.** **If you believe one must
  change, STOP and say why.**
- **Do not land A1, A3, A4, A5, A6 or A7.** **A2 only.** **A landing that
  quietly grows is a landing nobody priced.**
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **Do not touch `agents/tasks/LJ-1-276/`.** **A SIBLING IS LIVE THERE**,
  landing step 6 as a different new master. **Your write territory and its
  write territory must not overlap.** **Yours is
  `src/L/Coding/Injection.lagda.md` and it is named; if the sibling's choice
  collides, yours is the named one and it wins.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the load beside every absolute figure.**
- **Create your report file in your FIRST five minutes (C-22).**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE RULES THIS CHAIN EARNED

**`exit 0` IS NOT A SUPPLY** (C-45). **`[LJ-1.263]` proved a landing by
re-running the probes against the master they had just landed into, and all
three exited 0.** **Do the same: after the master is green, re-run something
that IMPORTS it.** **A copy that compiles is not a landing.**

**C-40. A new master has consumers the moment it exists.**

**C-49, written today.** **A heap wall and a rate can be properties of the
LAYOUT rather than the content.** **You are landing in a NEW master and that is
why.**

**C-44. A brief's claim is unchecked until you check it.** **Every figure in
this brief is another report's.**

**P-t. An average hides the term.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.227]` measured A2 TOWER-NEUTRAL on the Def-against-J axis.** **So
write it generic and say what a J instantiation would need.**

**And NAME YOUR AXIS** (C-46). **`[LJ-1.272]` measured that 12 of 62 DD4
figures in this phase carry no axis, and that DD4's OWN axis is
AC-against-GCH, fixed in code at `scripts/ledger.py:50`.** **Say, on THAT
axis, whether this master will sit inside the shared intersection or on the
GCH side alone.** **`[LJ-1.274]` computed that the AC root's import list at
`src/L/Model.lagda.md:49-57` does not reach the new A-prime masters; check
that and say what it means for this one.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-229/ProbeLJ1229A.agda`, read WHOLE. The content.**
- **`agents/tasks/LJ-1-229/lj-1.229-report.md`**: the block's own price and
  what it separated.
- **`agents/tasks/LJ-1-268/lj-1.268-report.md:23-48`**: the landing order and
  the no-extension finding.
- **`agents/tasks/LJ-1-263/lj-1.263-report.md`**: **how a landing was done and
  PROVED in this campaign.** **Copy the method.**
- `agents/tasks/LJ-1-134/`: the 78-line core measurement A2 grew from.
- **`archive/dev/TASKS-archived.md` and `archive/src/2026-08-09-rud-route/`.**
  **The retired route had coding modules too. Take SHAPE from the archive,
  never a claim**, and say what would NOT transfer.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md` splits II.5 into twelve rows.** **Say which
row A2 serves.** Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-229/ProbeLJ1229A.agda` FIRST, whole.

## SCOPE (write)

`src/L/Coding/Injection.lagda.md`, new, and `agents/tasks/LJ-1-277/` for your
report and any working file. **No existing master. Never
`src/Everything.lagda.md`.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for build` and read every statement.
**The tool prints `Full entry: dev/LESSONS.md:<line>` for every rule and says
THIS IS AN EXCERPT when it truncated. OPEN the full entry for any law you act
on.**

- **P-h.** Definability walks are module-parameterized, never
  function-parameterized.
- **P-k.** A read lemma is stated where its consumers use it. **The centre of
  your export decision.**
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
- **`lint-agda.py` binds a MASTER and did not bind the probe.** **Expect to
  trim the using lists.**
- **DD23 freezes mathematical prose.** **Write code and its own comments only.**
- **No em dash in any language.** Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with the delivered line count, the cold elapsed seconds, and the rate
against 0.010514.** Then what the master exports and what it keeps private,
with the consumer for each. Then the exact `src/Everything.lagda.md` line I
must add. Then the re-run that PROVES this is a landing. Then every existing
master you did not edit. Then the DD4 answer on the AC-against-GCH axis.
**Mark every negative MEASURED or INFERRED.**
