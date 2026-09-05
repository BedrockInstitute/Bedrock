# LJ-1.322: price all three cost mechanisms in four flag runs

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## WHAT THIS IS

**`[LJ-1.320]`'s ruling funds exactly this task and no other on the seconds
table.** The three candidate mechanisms behind
`src/L/Condensation.lagda.md`'s cost are ranked, **and every test is a FLAG**,
so this whole task edits no code.

**THE MACHINE MUST BE QUIET.** AGENTS.md: a task that measures check time gets
a quiet machine. **This task was held twice for that reason.** **Count the slots
and report the load before and after every run**, and say plainly if the machine
was not quiet.

## THE STANDING FACTS, and you re-derive each one (C-44)

| claim | anchor |
|---|---|
| DD24's bar is 0.010514 s per line | `dev/ledger.toml:292-297` |
| the gap is 60.0 s | `dev/ledger.toml:302-304` |
| `src/L/Condensation.lagda.md` is 132.28 s | a quotation chain, `[LJ-1.218]` kept by `[LJ-1.222]`; **run A1 re-measures it** |
| that is 71.4 percent of the GCH wing's 185.41 s | arithmetic |
| 117 module applications in that file | `[LJ-1.317]`, and `[LJ-1.320]` re-grepped it |
| zero `no-eta-equality` in that file | same |

## THE FOUR RUNS, in this order

**A1. Baseline, `--profile=definitions`.** Re-measures 132.28 s. **Prices the
`KFacts` consumers at `:6160`, `:6449`, `:6550`, `:6578`, `:6847` and `:7109`,
and the thirty `Agree` modules' definitions**, which is the `RowTies` gate. **It
is also the same-day control for B and C.**

**A2. Baseline, `--profile=internal`.** **Rank 2's test.** Read `Serialization`
plus `Import` against `Typing.CheckRHS`. **The comparable on record is
`[LJ-1.281]`'s 90.7 s of 100.8 s in `CheckRHS`.**

**B. `--no-syntactic-equality --profile=definitions`.** **Rank 1's test**, and
the cheapest possible cure if it wins. **The flag affects interface reloading,
so force a re-check of the module and report any dependency re-checks it
triggers.** **Report whether the flag co-exists with `--safe`**, which the 2.8.0
options page leaves unstated.

**C. `--lossy-unification --profile=definitions`.** **Rank 3's flag test.** **If
the run goes red, report the arm UNMEASURABLE, not a wall**: the heuristic is
documented sound but incomplete.

**AFTER the runs, restore the interface cache with one flagless check**, and
**leave no undeclared file in `_build/`** (`dev/build-manifest.toml` declares a
file's class when you create it).

**BEFORE dispatch of the runs: read the raw `.out` files of `[LJ-1.283]`'s
existing Condensation profile and check their bytes-currency by commit.** **If
current, they pre-answer the `RowTies` gate and cross-check A1**, and you may
save a run.

## THE DECISION TABLE, fixed NOW (D-1), and it is the ruling's

| measured branch | what follows |
|---|---|
| **B cuts the file's own Total by 30 s or more** | **Rank 1 CONFIRMED and it is the funded line.** Ranks 2 and 3 drop to unfunded |
| **B cuts less than 30 s, and A2 shows `Serialization` plus `Import` at 30 percent or more** | **Rank 2 leads** |
| **B and A2 both miss, and C cuts 30 s or more while staying green** | **Rank 3 leads** |
| **all three miss** | **All three mechanisms are REFUTED at this site.** Return to C-50 triage on A1's charged rows, which already name `satGraphB`, `twelveB` and `closedBS` |

**The 30 s threshold is half the 60.0 s gap**, and the ruling gives its reason:
a mechanism worth less than half the gap cannot be THE funded line while the
attribution rows already name concrete definitions.

## THE `RowTies` GATE, also fixed now

**Sum A1's charges over the `KFacts` consumers and the thirty `Agree`
modules.** **At 15 s or more, a `RowTies` PROBE is funded, not the build. Under
15 s, the compression is REFUSED for seconds** and the lines case returns to
DD13 pricing after `[LJ-1.306]` wave 2. **Do not stop `[LJ-1.306]`.**

## THE MEASUREMENT DISCIPLINE THIS PROJECT JUST WROTE, and it binds you

**C-53, `dev/LESSONS.md`, written 2026-08-15 from this very chain:**

- **Read a not-charged verdict from the RAW profile output, never from a
  report's excerpt.** A report prints a selected table and an absence in an
  excerpt is not an absence.
- **`Miscellaneous` is the profiler's EMPTY account**, measured at 54 to 61
  percent on this project's own runs and never mentioned in the 2.8.0 manual.
  **Every definitions-profile verdict you report states the Total, the
  `Miscellaneous` share, and a same-run charged control.**

**C-52: name the discriminating property, not a token.** **C-50: profile before
you cure.**

## THE ABORT CRITERION (D-1)

- **A BRANCH OF THE TABLE FIRES.** Report it, with all four runs' figures. STOP.
  **The next dispatch is the cure brief and it is not yours.**
- **ALL THREE MISS.** **A real answer and the ruling names what follows.**
- **THE MACHINE IS NOT QUIET.** **Say so and report the runs as INDICATIVE
  rather than measured.** **Do not silently publish a noisy figure.**
- **A FLAG IS INCOMPATIBLE WITH `--safe`.** **Report it; that would make the
  cheapest cure unavailable to this project whatever it measures.**
- **A WALL.** A single `agda` invocation past 30 MINUTES is a wall: interrupt,
  report ELAPSED SECONDS, bisect. **NEVER raise the cap.**

## WHAT YOU MUST NOT DO

- **EDIT NO CODE.** Every test here is a command-line flag. **`src/` is not
  yours** and this task proposes no cure.
- **Write only in `agents/tasks/LJ-1-322/`.** Do not touch another task
  directory.
- **COUNT THE AGDA SLOTS BEFORE EVERY INVOCATION.** C-12 caps this machine at
  TWO. **`ps aux | grep -c '[a]gda '` OVER-COUNTS (the bash wrapper) and
  `grep -c 'libexec.*bin/agda'` over-counts too (the grep). MEASURED
  2026-08-15.** Use:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
  **A sibling (`[LJ-1.325]`) is live and runs NO Agda by its brief. If the count
  is not 0 before a timing run, say so in the report beside that figure.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-322/lj-1.322-report.md` in your FIRST five
  minutes** and fill each run's figures in as it lands (C-22). **A four-run task
  that loses run three has lost everything if it wrote nothing down.**
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` on what you write.
  **No em dash in any language.**
- Evidence is `file:line` or a run's own output path. Write ASD-STE100. Mark
  every negative **MEASURED** or **INFERRED**, in those words.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **This task writes no code.**

**NAME THE AXIS** (C-46). DD4's own axis is AC-against-GCH, fixed in code at
`scripts/measure/ledger.py:50`. **`[LJ-1.320]` ruled that a `Condensation` cure
serves the GCH end alone, and that P-y's shared-code warning runs in REVERSE
here, which is good news: the file is in the judged side only, so every second
saved improves the DD24 ratio.** **VERIFY that, and note
`dev/ledger.toml:204`: the GCH closure is read from a STATEMENT whose proof is
not wired, so it UNDERSTATES.**

**AND THE STATEMENT CHANGED LAST NIGHT.** `src/L/GCH.lagda.md` was restated by
the `[LJ-1.323]` ruling. **Re-run the closure rather than quoting an older
figure**, because the trophy's import closure may have moved.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-320/lj-1.320-ruling.md`, read WHOLE.** It funds you and
  its decision table is above, verbatim.
- **`agents/tasks/LJ-1-317/lj-1.317-report.md`**, the three ranked mechanisms
  with their issue numbers and symptoms.
- **`agents/tasks/LJ-1-283/lj-1.283-report.md`** and its raw `.out` files, the
  existing Condensation profile.
- **`agents/tasks/LJ-1-311/lj-1.311-report.md`**, which measured that an
  excerpt, not the profiler, hid a charge.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim: the
  retired route had its own seconds crisis.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`agents/tasks/LJ-1-317/lj-1.317-report.md` carries the corpus**, which is a
proof assistant's rather than a mathematician's: agda issues 5801, 1646 and
6509, and the 2.8.0 options page. **Say in one line whether any of them states a
figure you can compare yours against.** Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-320/lj-1.320-ruling.md` sections 4 and 5 FIRST.

## SCOPE (write)

`agents/tasks/LJ-1-322/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement. **The tool prints `Full entry: dev/LESSONS.md:<line>` and says THIS
IS AN EXCERPT when it truncated. OPEN the full entry for any law you act on.**

- **D-1.** The decision table is fixed above.
- **C-50, C-52, C-53, C-44, P-l.** Named above with what each governs.
- **C-12.** Two Agda processes, counted with the command above.
- **R-41 as amended and CLOSED, P-y, C-49, C-51.**
- **C-22, C-32, C-39, C-42.** I-5. **D-8, D-26.**
- **DD0, DD4, DD8, DD18, DD24.**

## RETURN

**Lead with ONE line: which branch of the decision table fired.** Then the four
runs' figures, each with Total, `Miscellaneous` share, and load before and
after. Then the `RowTies` gate's sum against its 15 s floor. Then whether the
`--no-syntactic-equality` flag co-exists with `--safe`. Then whether the machine
was quiet. **Mark every negative MEASURED or INFERRED.**
