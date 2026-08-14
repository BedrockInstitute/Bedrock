# LJ-1.259: build the env closure, the one L-row nobody priced

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **The clock selected the mode.**

## GOAL

**`[LJ-1.258]` built 12 of 15 and the three that failed share ONE missing
hypothesis. It named it (C-36):**

```agda
envConsK : {k} (g : Fin k → V ℓ) (x : V ℓ)
         → env g ∈ K → x ∈ K → env (cons x g) ∈ K
```

**Build it.** **`consAtL-adequate` turns the satisfaction into
`e' ≡ env (cons x g)` with `z ≡ env g`, and the last step needs exactly
this.**

**`[LJ-1.258]` states the honest forms of all three `consK-*` and MEASURED
that they typecheck GIVEN the hypothesis**
(`agents/tasks/LJ-1-258/ProbeLJ1258.agda:288-337`, module `ConsK`). **So this
one lemma closes three fields.**

## WHY THIS IS THE SECOND HOLE OF THE SAME SHAPE

**`[LJ-1.258]` says it plainly: the env closure is「an L-row the nine-lemma
table did not price, analogous to the `sucK`/`union∈Lset-suc` hole
`[LJ-1.256]` found」.**

**So step 6's real cost is the 255 plus the L-rows nobody counted, and TWO are
now named.** **Price this one and the pattern is measured rather than
suspected.**

## WHAT `[LJ-1.258]` MEASURED, so you do not re-derive it

- **Body lines per field, per group: 2, 1, 1.** **Far UNDER `255 / 28 = 9.1`,
  by a factor of five to nine.**
- **Amortized over each group's shared proof: 6, 7, 3.** Around or under 9.1.
- **`[LJ-1.168]`'s 1.5-line entry estimate HOLDS**, measured at 1 to 2 body
  lines.
- **NONE of the fifteen is per-tower.** All are stated over `(K, Ktr)` from
  their first line, so the J tower re-instantiates unchanged.

**Do not re-measure any of that. Measure the closure.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **IT BUILDS AND THE THREE CLOSE.** Report the closure's lines, the three
  fields' body lines, and the seconds. **Then 15 of 15 are green in this
  group, and step 6's remaining cost is `[LJ-1.257]`'s eleven plus the two
  unpriced L-rows.** STOP.
- **IT BUILDS AND THE THREE DO NOT CLOSE.** **`consK-exist` carries a SECOND,
  different defect by `[LJ-1.258]` section 3.** **Name it** (C-36).
- **IT NEEDS SOMETHING ELSE.** **Name the term at `file:line`.** **A second
  missing L-row is a real finding and it prices the pattern.**
- **IT IS ALREADY DELIVERED.** **Check `src/` before you write a line.**
  **Three times this week a report called something absent that the tree or the
  archive held**, and `[LJ-1.256]` found `someEnv`'s blocker delivered in four
  lines. **`env` and `cons` are delivered; the closure may be too.**
- **A WALL.** **A single `agda` invocation past 20 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **Your control is
  `ProbeLJ1258.agda`.**

## WHAT YOU MUST NOT DO

- **Do not rebuild the twelve.** They are green.
- **Do not build `[LJ-1.257]`'s eleven or `someEnv`.** A sibling has them.
- **Do not edit any master.** **READ them freely.** **Nothing lands in `src/`,
  and a probe under `src/` is forbidden by I-5.**
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **Do not touch `agents/tasks/LJ-1-257/`.** A sibling is live there.
- **A probe goes in `agents/tasks/LJ-1-259/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the load beside every absolute figure**, discard a warm-up, take three kept
  runs for any figure a decision rests on.
- **Report a heap exhaustion as a wall.** Never raise the cap.
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## SEVEN RULES THIS CHAIN EARNED

**CHECK THE TREE BEFORE YOU CALL SOMETHING ABSENT.** **Three times this week.**

**FIVE COPIES OF ONE PROOF ARE ONE OBSERVATION.**

**A PROHIBITION IN A BRIEF CAN BE THE WHOLE BLOCKER** (C-39). **One of mine
was.**

**SEARCH THE OPEN-WORK LIST BY CONTENT, NOT BY NAME.**

**A FAILED SUBSTITUTION IS NOT A PROOF OF IMPOSSIBILITY** (C-36).

**`exit 0` IS NOT A SUPPLY** (C-45).

**C-44: if THIS brief states anything you cannot find, say so and treat it as
unproven.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.258]` MEASURED that none of its fifteen is per-tower and that all are
stated over `(K, Ktr)` from line one.** **`env` and `cons` name no tower
either.** **So write the closure over `(K, Ktr)` too, and say whether it stayed
neutral.** **If it did, the J tower pays this L-row once and step 6's
per-tower share stays near the 25 lines `[LJ-1.256]` measured.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-258/lj-1.258-report.md` and `ProbeLJ1258.agda`**, read
  WHOLE. **Its module `ConsK` at `:288-337` states the three honest forms and
  is your specification.**
- `agents/tasks/LJ-1-256/lj-1.256-report.md`: the other unpriced L-row, and
  the method for checking a delivered supplier.
- `agents/tasks/LJ-1-254/`: `envSetK`, `sucK`, `union∈Lset-suc`.
- `agents/tasks/LJ-1-168/`: the nine-lemma table that priced neither hole.
- **`src/L/Coding/Environment.lagda.md` and `src/L/Condensation.lagda.md`:
  read where `env` and `cons` are delivered, at the source.**
- **`archive/dev/TASKS-archived.md`.** **Take SHAPE from the archive, never a
  claim.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**Say in one line whether the literature needs an environment closure at this
point or takes it for granted.** Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-258/lj-1.258-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-259/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for build`. **The
tool now prints `Full entry: dev/LESSONS.md:<line>` for every rule and says
THIS IS AN EXCERPT when it truncated. OPEN the full entry for any law you act
on.**

- **D-1.** The abort criterion is fixed above.
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
- **C-36.** Write the term you could not write.
- **C-44, C-45.** A claim is unchecked until you check it; audit the
  instantiation.
- **P-l, C-39, C-40, C-42. P-i, R-40, R-34, I-5. C-12, C-22. P-k, P-m, P-t,
  P-y. DD0, DD8, DD18, DD24, D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with whether `envConsK` builds and whether the three `consK-*` close
with it.** Then its lines and the three fields' body lines. Then
`consK-exist`'s second defect. Then whether the closure was already delivered.
Then the seconds with load and run count. Then whether it stayed
tower-neutral. **Mark every negative MEASURED or INFERRED.**
