# LJ-1.255: build the eleven fields `envSetK` unlocks

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **The clock selected the mode.**

## GOAL

**`[LJ-1.254]` built the join and it is green.** `envSetK`, the term
`[LJ-1.199]` stopped on at ZERO lines, typechecks: `ar ≡ # n` plus the
delivered `envSetNumeral∈` plus `NumeralFromGeneric.derived` plus the `succλ`
climb give `Generic.envSetGen B₀ ar ∈ Lset lam`.

**And `envSetK` is NOT one of the 28. It sits BENEATH eleven of them**
(`[LJ-1.254]` section 3, and `[LJ-1.199]` section 5 named the same eleven).

**Build those eleven.**

| group | count | term needed | delivered reader |
|---|---:|---|---|
| `envK-mem`, `envK-neg`, `envK-top`, `envK-imp`, `envK-allin` | 5 | `E ∈ K` from `⊨ envSetAt` | `Generic.Holds.bwd` + `envSetK` + `transK` |
| `envInK-mem`, `envInK-neg`, `envInK-top`, `envInK-imp` | 4 | `z ∈ K` from `⊨ envOverAt` | `Generic.Holds.bwd` + `envSetK` + `transK` |
| `someEnv` | 1 | an environment `E ∈ K` with `envHypB2`, from three K memberships | `Generic.Holds` + `envSetK`; **the construction itself is UNMEASURED** |
| `t0eq`, `t1eq` | 2 | slot equalities at the consumer's own `t0`/`t1` | **the consumer's site states them; the supply pays ZERO, INFERRED** |

**Twelve rows, eleven fields plus the two slot equalities, and `[LJ-1.254]`
marks `someEnv`'s construction UNMEASURED and `t0eq`/`t1eq` as INFERRED
zero-cost. Check both.**

## WHAT IS GREEN, so you extend rather than rebuild

| file | what it is |
|---|---|
| `agents/tasks/LJ-1-254/ProbeLJ1254.agda` | `envSetK`, `sucK`, `union∈Lset-suc`, 141 in-fence lines, exit 0 |
| `agents/tasks/LJ-1-252/ProbeLJ1252A.agda` | `ω∈λ-from-α`, the five-line join, exit 0 |

**Start from `ProbeLJ1254.agda`. Do not rebuild `envSetK` or `sucK`.**

## THE FIGURE THIS TASK OWES

**`[LJ-1.254]` wrote 141 in-fence lines for ONE field plus TWO supporting
lemmas, against 255 for all 28.** **Those two lemmas are one-time.**

**So the number that matters is the MARGINAL cost per field, and nobody has
it.** **Report the eleven fields' lines APART from any shared setup.** **That
one figure decides whether the 255 holds for the remaining 27.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **ALL ELEVEN BUILD.** Report the marginal lines per field and the seconds.
  **Then 12 of 28 are green, the 255 has a real rate behind it, and I dispatch
  the remaining 16.** STOP.
- **N OF ELEVEN BUILD.** **Report N and name what each remaining field needs**
  (C-36). **A named residue beats an estimate.**
- **`someEnv` IS DEARER THAN THE OTHERS.** **`[LJ-1.254]` marked its
  construction UNMEASURED and it is the one row without a clean reader.**
  **Price it apart from the ten.**
- **`t0eq`/`t1eq` ARE NOT FREE.** **`[LJ-1.254]` INFERRED they cost zero
  because the consumer's site states them.** **If that is wrong, say so: it is
  exactly the「exit 0 is not a supply」shape** (C-45).
- **THE MARGINAL RATE BREAKS THE 255.** If eleven fields cost far more than
  `255 / 28` per field, **say so with both figures.** **That re-prices step 6
  and it is a complete answer.**
- **A WALL.** **A single `agda` invocation past 20 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **`[LJ-1.254]` measured that
  `sucK` does NOT wall at this site, so a wall here would be a new one and
  worth naming.**

## WHAT YOU MUST NOT DO

- **Do not build the other 16 fields.** `[LJ-1.254]` section 3 names their
  terms and they are the next dispatch.
- **Do not re-derive the join.** `envSetK` is green.
- **Do not edit any master.** This is a probe. **Nothing lands in `src/`, and a
  probe under `src/` is forbidden by I-5.** **The telescope addition
  `[LJ-1.252]` priced is a MASTER change and I sequence it.**
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **A probe goes in `agents/tasks/LJ-1-255/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the load beside every absolute figure**, discard a warm-up, and take at least
  three kept runs for any figure a decision rests on.
- **Report a heap exhaustion as a wall.** **`[LJ-1.234]` met one that was
  R-34's unpinned `InfinitySet` level meta, cured by
  `module IS = InfinitySet {ℓ}`.**
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## SIX RULES THIS CHAIN EARNED

**SEARCH THE OPEN-WORK LIST BY CONTENT, NOT BY NAME.**

**A FAILED SUBSTITUTION IS NOT A PROOF OF IMPOSSIBILITY** (C-36), **and a
READING is weaker still.** **`[LJ-1.199]` stopped this whole layer by reading
and two probes reopened it.**

**`exit 0` IS NOT A SUPPLY** (C-45). **Audit the instantiation.**

**THE ARCHIVE BEARS UNTIL YOU OPEN IT.**

**CARRY A CLAIM'S QUALIFIER OR CARRY NEITHER.**

**C-44: if THIS brief states anything you cannot find, say so and treat it as
unproven.** **The twelve-row table above is `[LJ-1.254]`'s reading, not its
build.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.113]:219-239` split the 28 into 25 coding machinery and 3 per-tower,
and `[LJ-1.254]` section 4 tested that split.** **Read its answer and say
whether your eleven fall where it put them.** **If the eleven are coding
machinery, they are shared and the J tower pays them once.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-254/lj-1.254-report.md` and `ProbeLJ1254.agda`**, read
  WHOLE. **Section 3's table is your specification and section 4 is the DD4
  answer.**
- **`agents/tasks/LJ-1-199/lj-1.199-report.md` section 5**: the same eleven,
  named before the join existed.
- `agents/tasks/LJ-1-168/`: the nine-lemma table `[LJ-1.254]` read whole.
- `agents/tasks/LJ-1-113/lj-1.113-report.md:219-239`: the 28 and the split.
- **`src/L/Condensation/TwelveAgree.lagda.md` and
  `src/L/Coding/Key.lagda.md:476`: read the source, never a report about it.**
- **`archive/dev/TASKS-archived.md`.** **Take SHAPE from the archive, never a
  claim.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**Say whether Devlin's construction needs these eleven environment facts or
whether they are an artifact of the coding.** Return a **LITERATURE USED**
section.

## SCOPE (read)

`agents/tasks/LJ-1-254/lj-1.254-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-255/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for build`.

- **D-1.** The abort criterion is fixed above.
- **P-l.** `[LJ-1.254]`'s 141 includes one-time setup and is NOT a per-field
  rate. **This task exists to produce that rate.**
- **C-36.** Write the term you could not write, per unbuilt field.
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
- **C-44, C-45.** A claim is unchecked until you check it; audit the
  instantiation.
- **P-i, R-40, R-34, I-5. C-12, C-22, C-39, C-40, C-42. P-k, P-m, P-t, P-y.
  DD0, DD8, DD18, DD24, D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with N of eleven built, and the MARGINAL lines per field apart from
shared setup.** Then `someEnv` priced apart. Then whether `t0eq` and `t1eq`
really cost zero. Then that rate against `255 / 28`. Then the seconds with load
and run count. Then the DD4 answer. **Mark every negative MEASURED or
INFERRED.**
