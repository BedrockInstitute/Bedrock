# LJ-1.268: the landing order for Route A-prime, because 1,089 lines are priced and none is delivered

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**. **This task runs
NO Agda and holds no slot, so the model rule would give flash. I override it
and record why: the task READS Agda probes and judges what each must import
before it can become a master, which the `--agda` flag cannot see.** The clock
selected the mode.

## GOAL

**Route A-prime is priced at 1,089 lines with a reading residue of ZERO, and
not one line of it is in `src/`.**

**I checked myself, by grep over `src/`:**

| object | block | in `src/` |
|---|---|---|
| `injAt` | A2 | **0** |
| `LeastCardInj` | A4 | **0** |
| `GCHStatement` | A7 | **0** |
| `IsCardinalL` | A4 | **0** |

**Every block exists as a GREEN PROBE and nothing more.** **Write the landing
order.**

## WHAT THE ORDER MUST SETTLE

**For each of the seven blocks:**

1. **WHICH MASTER does it land in**, new or existing, and why.
2. **WHAT DOES IT IMPORT** that is not yet delivered. **A block whose imports
   are all delivered can land today; a block that imports another block's
   probe cannot land before it.**
3. **WHAT DOES `src/Everything.lagda.md` NEED**, in one line per block. **I
   wire that file and no agent touches it, so name what I must add.**
4. **WHAT BREAKS IF IT LANDS FIRST.** C-40: a new master has consumers the
   moment it exists.

**Then give the ORDER as a list, and say which blocks can land in parallel.**

## THE BLOCKS AND THEIR PROBES

| block | lines | probe |
|---|---:|---|
| A1 | 54 | `agents/tasks/LJ-1-232/ProbeLJ1232A1.agda` |
| A2 | 186 | `agents/tasks/LJ-1-229/ProbeLJ1229A.agda` |
| A3 | 26 | `agents/tasks/LJ-1-232/ProbeLJ1232A3.agda` |
| A4 | 43 | `agents/tasks/LJ-1-236/ProbeLJ1236A4.agda`, **a MINIMAL CORE** |
| A5 | 348 | rows 2 and 4 DISSOLVED; row 5 at `agents/tasks/LJ-1-234/ProbeLJ1234A.agda`; row 1 at `agents/tasks/LJ-1-264/` |
| A6 | 399 | `agents/tasks/LJ-1-217/ProbeLJ1217A.agda` |
| A7 | 33 | `agents/tasks/LJ-1-236/ProbeLJ1236A7.agda` |

**`[LJ-1.236]` measured that A7's statement audits the rest: A5's `sq` and
A6's `absorbs` have conclusion types that are A7's hypotheses on the nose.**
**`[LJ-1.136]` section 6.1 ruled the statement should be written SECOND.**
**So A7 may belong early in the order even though it is the trophy.**

## THE ONE THING THAT MAKES THIS URGENT RATHER THAN TIDY

**`[LJ-1.266]` is measuring right now what step 6's roughly 400 lines cost in
SECONDS inside `src/L/Condensation.lagda.md`, which runs at 1.9x the bar.**

**A-prime's 1,089 lines land somewhere too, and nobody has said where.** **If
they land in masters already over the bar, the wing's 60.0 s gap grows on the
day of the landing. If they land in new masters or in the eight that are under
the bar together, it may not.**

**So say, per block, WHICH SIDE OF THE BAR its destination master sits on
today.** `[LJ-1.218]`'s per-master table has every rate.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **AN ORDER EXISTS AND EVERY BLOCK HAS A HOME.** Give it. **Then I sequence
  the landings and the phase stops being a pile of probes.** STOP.
- **A BLOCK HAS NO HOME.** **Say which and why.** **A block that needs a new
  master is a different decision from one that extends an existing file, and
  the owner should hear which.**
- **THE ORDER IS FORCED TO ONE SEQUENCE.** Say so, and say what forces it.
  **A forced sequence is a schedule; a partial order is a plan.**
- **A BLOCK CANNOT LAND AT ALL YET.** **A4 is a MINIMAL CORE by `[LJ-1.236]`'s
  own words, and A5's row 3 has never been built.** **Name every block that is
  not landable and what it still needs.**

## WHAT YOU MUST NOT DO

- **DO NOT RUN AGDA.** A sibling holds an Agda slot and is measuring seconds.
- **Do not land anything.** **You write the order. I sequence it.**
- **Do not re-price any block.** All seven are measured and `[LJ-1.253]` summed
  them to 1,089.
- **Do not edit any master, brief or report.** **Write your own report and
  nothing else.**
- **Do not touch `agents/tasks/LJ-1-266/` or `LJ-1-267/`.** Siblings are live.
- **Create your report file in your FIRST five minutes (C-22).**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## EIGHT RULES THIS CHAIN EARNED

**`exit 0` IS NOT A SUPPLY** (C-45). **A green probe is not a delivered
master, and `[LJ-1.263]` proved the difference by re-running three probes
against the master they had just landed into. Your order should say, per
block, what that re-run would be.**

**C-40: a new master has consumers the moment it exists.**

**DERIVE A FIGURE OR DO NOT WRITE IT** (C-44). **The grep table above is
mine and I ran it; everything else in this brief is another report's.**

**SEARCH THE OPEN-WORK LIST BY CONTENT, NOT BY NAME.**

**THE ARCHIVE BEARS UNTIL YOU OPEN IT.**

**A FAILED SUBSTITUTION IS NOT A PROOF OF IMPOSSIBILITY** (C-36).

**AN ESCAPE HATCH IS THE SHAPE A WRONG CHOICE HIDES IN** (C-43).

**A LINE LEVER AND A SECONDS LEVER ARE DIFFERENT LEVERS** (P-q).

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.248]` measured A-prime's per-tower half at 146 to 196 lines, a BAND
because the partition is a survey and excludes A5.** **`[LJ-1.227]` measured A2
and A7 TOWER-NEUTRAL and A1, A3, A4 PER-TOWER.**

**So the landing order is also a DD4 decision: a tower-neutral block should
land in a place the J tower can re-instantiate, and a per-tower block should
not pretend to.** **Say, per block, where it lands ON THAT BASIS**, and **NAME
YOUR AXIS**: `[LJ-1.262]` measured that this phase mixes Devlin's
Def-against-J with the port's L-against-ambient.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-253/lj-1.253-report.md`**, read WHOLE: the 1,089 and
  every block's basis.
- **`agents/tasks/LJ-1-248/lj-1.248-report.md`**: the caliber question, which
  is your question 2 in another form.
- **`agents/tasks/LJ-1-218/lj-1.218-report.md`**: the per-master seconds table,
  for the bar-side question.
- `agents/tasks/LJ-1-236/`, `LJ-1-232/`, `LJ-1-229/`, `LJ-1-217/`, `LJ-1-234/`,
  `LJ-1-264/`: the seven probes.
- `agents/tasks/LJ-1-263/lj-1.263-report.md`: how a landing was done today,
  including the re-run that proved it.
- **`src/Everything.lagda.md`: READ it to see what a wiring line looks like.
  Do not edit it.**
- **`archive/dev/TASKS-archived.md` and `archive/src/2026-08-09-rud-route/`.**
  **The retired route landed a trophy and its file layout is a SHAPE. Take
  shape, never a claim**, and say what would NOT transfer.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**Say in one line whether the literature suggests a file layout for II.5's
twelve rows**, or whether the layout is purely an engineering choice. Return a
**LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-253/lj-1.253-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-268/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for recon` and read every statement.
**The tool prints `Full entry: dev/LESSONS.md:<line>` for every rule and says
THIS IS AN EXCERPT when it truncated. OPEN the full entry for any law you act
on.**

- **C-40.** **Verify the CONSUMERS. A new master has them the moment it
  exists.**
- **C-45.** Audit the instantiation, never the telescope.
- **C-44.** A brief's claim is unchecked until you check it.
- **P-k.** A read lemma is stated where its consumers use it. **That is the
  home question.**
- **P-q.** A line lever and a seconds lever are different levers.
- **D-10.** Price the truth of a recorded residue before pricing its proof.
- **P-l, D-26. C-22, C-32, C-36, C-39, C-42, C-43. I-5. DD0, DD8, DD18,
  DD24.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `.venv/bin/python scripts/lint-prose.py --check` on your report.
- **No em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with the ORDER as a list, and say which blocks can land in parallel.**
Then one section per block: its home master, its undelivered imports, its
`Everything.lagda.md` line, and which side of the bar its destination sits on
today. Then every block that cannot land yet and what it needs. Then the DD4
answer per block WITH ITS AXIS NAMED. **Mark every negative MEASURED or
INFERRED.**
