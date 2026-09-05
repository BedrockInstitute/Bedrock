# LJ-1.258: the fifteen fields that do not touch `envSetK`

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **The clock selected the mode.**

## GOAL

**`[LJ-1.254]` section 3 named every one of step 6's 28 fields with the term it
needs and the DELIVERED reader that supplies it.** **Eleven of them sit on
`envSetK` and are `[LJ-1.257]`'s. Two, `t0eq` and `t1eq`, are MEASURED zero.
`sucK` is built.**

**Fifteen remain and NONE of them touches `envSetK`. Build them.**

| group | count | term needed | delivered reader |
|---|---:|---|---|
| `valK`, `valK-un` | 2 | `yc ∈ K` from the code equation | `domEntryK` / `closedEntryK` (KFacts fields) + `transK` |
| `valV`, `valW`, `wKfact` | 3 | `v/w ∈ K` from `⊨ tmValAt` | `tmValAt-out` + `transK` |
| `subK₁-and`, `subK₀-and`, `subK₁-imp`, `subK₀-imp`, `subK-neg`, `subK-un`, `subK-allin` | 7 | `y ∈ K` from `⊨ subValAt` / `subValSuccAt` | `subValAt-adequate`, `subValSuccAt-adequate` + `transK` / `sucK` |
| `consK-exist`, `consK-forall`, `consK-allin` | 3 | `e' ∈ K` from `⊨ consAtL` | `consAt-adequate`, `DenoteBody-out` + `transK` |

**Every reader in that table is DELIVERED. `transK` and `sucK` are green in
`agents/tasks/LJ-1-254/ProbeLJ1254.agda`.**

## THE FIGURE THIS TASK OWES, and it is the one that settles step 6

**`[LJ-1.256]` OVERTURNED `[LJ-1.255]`'s rate because five copies of one proof
are ONE observation.** **These fifteen are FOUR different groups.**

**So this task is the real sample.** **Report the marginal lines PER GROUP, not
one average.** **Four groups measured apart is what `255 / 28 = 9.1` has to be
tested against, and nothing before this had it.**

## SHARE BEFORE YOU COPY

**`[LJ-1.256]` measured that `[LJ-1.255]`'s five bodies were one proof written
five times and that the tree already carries a slot-generic module for exactly
that.** **Within each of your four groups, write the proof ONCE and instantiate
it.** **If a group cannot share, say why at `file:line`: that is a finding
about the group and it re-prices it honestly.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **ALL FIFTEEN BUILD.** Report the four per-group rates and the seconds.
  **Then 28 of 28 are green once `[LJ-1.257]` lands, step 6 is DONE, and phase
  1's blocking row moves.** STOP.
- **N OF FIFTEEN BUILD.** **Report N per group and name what each remaining
  field needs** (C-36). **A group that fails whole is a different finding from
  a field that fails alone: say which.**
- **A DELIVERED READER DOES NOT REACH.** **`[LJ-1.254]` named these readers by
  READING, not by building.** **If one does not supply what the table says, say
  so at `file:line`.** **That is C-44 and it is the likeliest defect here.**
- **A GROUP NEEDS A MISSING HYPOTHESIS.** **The four `envInK-*` needed a
  numeral premise `TFacts` does not carry. If a group here has the same
  disease, name it** and do NOT change the master.
- **A WALL.** **A single `agda` invocation past 20 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **`sucK` did NOT wall at this
  site (`[LJ-1.254]`), and the `subK` group is the one that uses it.**

## WHAT YOU MUST NOT DO

- **Do not build the eleven `envSetK` fields or `someEnv`.** `[LJ-1.257]` has
  them.
- **Do not edit any master.** **READ them freely.** **Nothing lands in `src/`,
  and a probe under `src/` is forbidden by I-5.**
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **Do not touch `agents/tasks/LJ-1-257/`.** A sibling is live there.
- **A probe goes in `agents/tasks/LJ-1-258/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the load beside every absolute figure**, discard a warm-up, take three kept
  runs for any figure a decision rests on.
- **Report a heap exhaustion as a wall.** Never raise the cap.
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## SEVEN RULES THIS CHAIN EARNED

**FIVE COPIES OF ONE PROOF ARE ONE OBSERVATION.** **That is why your report
must give four rates and not one.**

**A PROHIBITION IN A BRIEF CAN BE THE WHOLE BLOCKER** (C-39). **One of mine
was, two dispatches ago.**

**SEARCH THE OPEN-WORK LIST BY CONTENT, NOT BY NAME.**

**A FAILED SUBSTITUTION IS NOT A PROOF OF IMPOSSIBILITY** (C-36).

**`exit 0` IS NOT A SUPPLY** (C-45).

**THE ARCHIVE BEARS UNTIL YOU OPEN IT.**

**C-44: if THIS brief states anything you cannot find, say so and treat it as
unproven.** **The table above is `[LJ-1.254]`'s READING and it built none of
these fifteen.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.113]:219-239` split the 28 into 25 coding machinery and 3 per-tower,
and `[LJ-1.256]` measured the three per-tower fields at about 25 lines, near 9
percent.** **Say which of YOUR fifteen are the per-tower ones**, if any, and
whether the rest name a tower anywhere. **A group that names no tower should be
written over a structure parameter from its first line.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-254/lj-1.254-report.md`**, read WHOLE. **Its section 3
  table is your specification and section 4 is the DD4 answer.**
- **`agents/tasks/LJ-1-255/` and `LJ-1-256/`**, read WHOLE: the rate that was
  refuted and the reason, so you do not repeat the shape.
- `agents/tasks/LJ-1-168/`: the nine-lemma table.
- `agents/tasks/LJ-1-113/lj-1.113-report.md:219-239`: the 28 and the split.
- **`src/L/Condensation/TwelveAgree.lagda.md` and the delivered readers named
  in the table: read the source, never a report about it.**
- **`archive/dev/TASKS-archived.md`.** **Take SHAPE from the archive, never a
  claim.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**Say in one line whether Devlin needs these fifteen facts or whether they are
an artifact of the coding.** Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-254/lj-1.254-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-258/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for build`. **The
tool now prints `Full entry: dev/LESSONS.md:<line>` for every rule and says
THIS IS AN EXCERPT when it truncated. OPEN the full entry for any law you act
on.**

- **D-1.** The abort criterion is fixed above.
- **P-l.** **One group's rate is not another group's rate. This task exists
  because that mistake was just made.**
- **C-36.** Write the term you could not write, per unbuilt field.
- **C-44, C-45.** A claim is unchecked until you check it; audit the
  instantiation.
- **C-38, C-39, C-40, C-42. P-i, R-40, R-34, I-5. C-12, C-22. P-k, P-m, P-t,
  P-y. DD0, DD8, DD18, DD24, D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with N of fifteen built and FOUR per-group marginal rates.** Then each
unbuilt field's term. Then any delivered reader that did not reach. Then those
four rates against `255 / 28 = 9.1`. Then the seconds with load and run count.
Then which fields are per-tower. **Mark every negative MEASURED or INFERRED.**
