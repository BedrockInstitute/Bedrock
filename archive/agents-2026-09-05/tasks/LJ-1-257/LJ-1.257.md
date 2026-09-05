# LJ-1.257: the four `envInK-*` and `someEnv`, which are not blocked after all

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **The clock selected the mode.**

## GOAL

**`[LJ-1.255]` reported the four `envInK-*` and `someEnv` BLOCKED.
`[LJ-1.256]` measured that BLOCKED overstates it, twice over.**

| what `[LJ-1.255]` said | what `[LJ-1.256]` MEASURED |
|---|---|
| the four `envInK-*` lack the numeral premise | **TRUE, and a real defect** in `[LJ-1.173]:843-846`, whose row 1 gave them `ar ∈ K` |
| they are therefore blocked | **FALSE.** The supplier is DELIVERED at `src/L/Coding/CodeSet.lagda.md:185-204`, and the block was MY brief's own no-master-edit rule |
| `someEnv` needs a 120-line adequacy | **FALSE.** Its second blocker is DELIVERED in FOUR lines at `src/L/Condensation.lagda.md:3042` |

**Build all five.**

## THE RULE THAT BLOCKED THEM WAS MINE, and it is lifted for the read only

**`[LJ-1.255]` could not use `src/L/Coding/CodeSet.lagda.md:185-204` because my
brief forbade touching a master.** **That rule stands for WRITING: nothing
lands in `src/` from this task either.**

**But READ it, import it, and use what it delivers.** **A delivered supplier is
not off-limits because it lives in a master.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **ALL FIVE BUILD.** Report their marginal lines and the seconds. **Then 10 of
  the 11, plus `t0eq`/`t1eq` at MEASURED zero, plus `sucK`, make 13 of 28
  green.** STOP.
- **N OF FIVE BUILD.** **Name what each remaining field needs** (C-36).
- **THE DELIVERED SUPPLIER DOES NOT REACH.** **`[LJ-1.256]` read
  `CodeSet.lagda.md:185-204` and judged it sufficient. If it is not, say so at
  `file:line`** and the defect is in that reading, not in your build.
- **THE NUMERAL PREMISE MUST BE ADDED TO `TFacts`.** **Then it is a MASTER
  change**: name every consumer of `TFacts` (C-40) and price it. **Do not make
  the change.**
- **A WALL.** **A single `agda` invocation past 20 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **Your control is
  `ProbeLJ1255.agda`.**

## THE SECOND DELIVERABLE, and `[LJ-1.256]` says the tree already proves it

**`src/L/Condensation.lagda.md:2926` is a SLOT-GENERIC `EnvSet` module, and its
own comment at `:2917-2925` says one copy serves every frame layout and BOTH
towers.**

**`[LJ-1.255]`'s five `envK-*` bodies are one proof written five times.**

**So: can the five collapse into one application of that module?** **Try it.**
**If they can, report the collapsed line count against the 85**, because that
is the number that decides step 6's marginal rate and `[LJ-1.256]` measured
that the copies are avoidable.

**If they cannot, say why at `file:line`.** **That is a finding about the
generic module and it is worth more than the collapse.**

## WHAT YOU MUST NOT DO

- **Do not edit any master.** **READ them freely.** **Nothing lands in `src/`,
  and a probe under `src/` is forbidden by I-5.**
- **Do not build the other 16 fields.** `[LJ-1.258]` has them.
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **Do not touch `agents/tasks/LJ-1-258/`.** A sibling is live there.
- **A probe goes in `agents/tasks/LJ-1-257/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the load beside every absolute figure**, discard a warm-up, take three kept
  runs for any figure a decision rests on.
- **Report a heap exhaustion as a wall.** Never raise the cap.
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## SEVEN RULES THIS CHAIN EARNED

**A PROHIBITION IN A BRIEF CAN BE THE WHOLE BLOCKER** (C-39). **It was, here,
and `[LJ-1.256]` caught it.**

**FIVE COPIES OF ONE PROOF ARE ONE OBSERVATION.**

**SEARCH THE OPEN-WORK LIST BY CONTENT, NOT BY NAME.**

**A FAILED SUBSTITUTION IS NOT A PROOF OF IMPOSSIBILITY** (C-36).

**`exit 0` IS NOT A SUPPLY** (C-45).

**THE ARCHIVE BEARS UNTIL YOU OPEN IT.**

**C-44: if THIS brief states anything you cannot find, say so and treat it as
unproven.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**The slot-generic `EnvSet`'s own comment says one copy serves BOTH TOWERS.**
**So the collapse above is a DD4 measurement and not only a line saving.**
**Say whether the collapsed form is tower-neutral**, and `[LJ-1.256]` measured
the three per-tower fields at about 25 lines, near 9 percent.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-256/lj-1.256-report.md`**, read WHOLE. **It is your
  specification and it names every delivered supplier.**
- **`agents/tasks/LJ-1-255/lj-1.255-report.md` and `ProbeLJ1255.agda`**, read
  WHOLE. **Your starting file.**
- `agents/tasks/LJ-1-254/`: `envSetK`, `sucK`, `union∈Lset-suc`.
- `agents/tasks/LJ-1-173/` sections around `:843-846`: the cure table's row 1
  defect.
- **`src/L/Coding/CodeSet.lagda.md:185-204`, `src/L/Condensation.lagda.md:2917-2926`
  and `:3042`, `src/L/Condensation/TwelveAgree.lagda.md:216-244`: read the
  source.**
- **`archive/dev/TASKS-archived.md`.** **Take SHAPE from the archive, never a
  claim.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**Say in one line whether Devlin needs these five facts or whether they are an
artifact of the coding.** Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-256/lj-1.256-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-257/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for build`. **The
tool now prints `Full entry: dev/LESSONS.md:<line>` for every rule and says
THIS IS AN EXCERPT when it truncated. OPEN the full entry for any law you act
on.**

- **D-1.** The abort criterion is fixed above.
- **C-39.** **A brief's prohibition binds harder than its goal. Mine did.**
- **C-40.** Verify the CONSUMERS of a changed record, never the record alone.
- **C-36.** Write the term you could not write.
- **C-44, C-45.** A claim is unchecked until you check it; audit the
  instantiation.
- **P-l, C-38, C-42. P-i, R-40, R-34, I-5. C-12, C-22. P-k, P-m, P-t, P-y.
  DD0, DD8, DD18, DD24, D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with N of five built, and with the collapsed line count for the five
`envK-*` against their 85.** Then each unbuilt field's term. Then whether the
`TFacts` numeral premise must be added and what it would cost at every
consumer. Then the seconds with load and run count. Then the DD4 answer.
**Mark every negative MEASURED or INFERRED.**
