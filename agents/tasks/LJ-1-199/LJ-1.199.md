# LJ-1.199: BUILD step 6, the satisfaction layer supply, priced at 255

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda, so it takes pro and holds an Agda slot.

## GOAL

**`[LJ-1.172]` refuted step 6 at the join. `[LJ-1.173]` swept that refutation to
21 false fields across three records, CURED all 21 for 77 lines, re-priced step
6 at about 255, and STOPPED before building it because I told it to.**

**Build it.**

## THE PRICE AND ITS BASIS, from `[LJ-1.173]`

**About 255 in-fence lines.** The basis is `[LJ-1.168]`'s nine-lemma allocation
with three lemmas re-costed against work already delivered:

- **L9, `envSetK`: 45 to 25.** `mkReflect` was refuted, and `envSetNumeral∈` is
  **DELIVERED** at `src/L/Coding/Key.lagda.md`. What remains is the `envSet` to
  `envSetGen` step.
- **L4, `envOverAt` to `z ∈ K`: 15 to 12.** `ar ∈ K` is now a HYPOTHESIS the
  field RECEIVES, not something the supplier must find.
- **L8: 30 to 25**, for the same discharge.
- **Plus 15 NEW** to supply `codesK`'s numeral component through
  `arityNumAtL-out`.
- The other six lemmas are untouched at `[LJ-1.168]`'s figures.

**That is an estimate with a named basis (DD8), not a measurement. Report the
actual against it, and record an overage plainly rather than working it down
silently.**

## WHAT THE TREE NOW GIVES YOU THAT IT DID NOT

**The 21 cured fields are LANDED and green**, across `TwelveAgree`,
`LowerAgree`, `UpperAgree` and `L/Condensation`. **So the hypotheses your
supply must discharge are the CURED ones**, and three facts arrive free that the
refuted version made you find:

1. **`ar ∈ K`** is a hypothesis the field receives.
2. **The numeral equation** arrives as `codesK`'s fourth component.
3. **`envSetNumeral∈`** is delivered at `src/L/Coding/Key.lagda.md:476`.

**Read the cured fields before you write, not the reports about them.**

## THE ONE THING THAT KILLED THE FIRST ATTEMPT AT THIS LAYER

**`[LJ-1.172]` built steps 1 to 5 and hit the join.** Its refutation was UPHELD
by an adversarial review (`[LJ-1.180]`), which re-derived every load-bearing
citation at the commit `[LJ-1.172]` measured. **So the join is real and the cure
is the one now in the tree.**

**If you reach a join that the cured fields still do not close, STOP and name
it.** That is a better return than a partial build, and it is what `[LJ-1.172]`
did.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **BUILT.** Report the lines against 255, the seconds, and whether the layer
  closes. STOP.
- **PARTIAL.** Land what is green and name exactly what is open. `[LJ-1.172]`
  landed 1 to 5 and that stood.
- **A NEW JOIN REFUTES.** Name the term you could not write, at `file:line`.
  **C-36.** `[LJ-1.172]`'s refutation was the most valuable return of its day.
- **A WALL.** **Report a heap exhaustion as a wall AND report a wall-clock
  wall.** A single `agda` invocation that passes **30 MINUTES** is a wall:
  interrupt it, report the elapsed seconds, and bisect. `[LJ-1.165]` measured a
  wall at 20 min 1 s, and on 2026-08-14 a sibling ran ONE typecheck for 3.06
  hours because its brief gave a heap cap and no clock cap. **That omission was
  mine and this line is the fix.**

## KEEP THE MINIATURE SMALL

**A sibling's probe reached 684 lines while its brief asked for the smallest
decisive miniature.** **Build in pieces that typecheck in minutes, not in one
file that typechecks in hours.** If a piece will not close, that piece is the
finding.

## WHAT YOU MUST NOT DO

- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **Do not undo any of the 21 cured fields.** They are green and committed.
- **A probe goes in `agents/tasks/LJ-1-199/`**, tracked, never deleted. **A
  build lands in `src/` only after you report the measurement to me.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** A sibling
  holds the other slot. **Report the load beside every absolute figure.**
- **A SIBLING'S FILE MAY BE RED WHILE YOU WORK. BUILD GENERIC FIRST.**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.
- **Create your report file in your FIRST five minutes and fill it as answers
  land (C-22).** A sibling died on 2026-08-14 having written nothing, and its
  reasoning had to be salvaged from its terminal.

## THE BAR

**DD24 unchanged and nothing tightens it** (owner, 2026-08-14): the bar was
FIXED when the AC trophy landed, every GCH module uses that one number, and
INTERMEDIATE DEBT IS ALLOWED because only the whole wing at the end is judged.
**Report lines and seconds as measured; never delete a line to improve a ratio.**

## THE INSTRUMENT

**`check-ratio.py` prints `noise band: at least +-12.8%, MEASURED [LJ-1.148]`,**
and `[LJ-1.185]` measured that a term three reports quoted for two days was a
DOUBLE SUBTRACTION and never existed. **A delta inside the band is no
measurement.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.184]` wrote a 167-line module naming ZERO tower or carrier names, with
both as parameters, and measured that SIX extra lines bought the second tower.**
**Write yours the same way and give the re-instantiation figure.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-173/lj-1.173-report.md`**, read WHOLE, especially its
  step 6 re-price and the nine-lemma table.
- **`agents/tasks/LJ-1-172/lj-1.172-report.md`**, read WHOLE: steps 1 to 5 as
  built, and the join it refuted.
- `agents/tasks/LJ-1-180/lj-1.180-report.md`: the adversarial review that UPHELD
  that refutation, and what it re-derived.
- `agents/tasks/LJ-1-168/lj-1.168-report.md`: the nine-lemma allocation this
  price is built on, and how 5,047 collapsed to about 270.
- **`archive/dev/TASKS-archived.md`.** **Take SHAPE from the archive, never a
  claim**, and say what would NOT transfer.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

`dev/literature/devlin-II5.md`, `devlin-errata.md`. **`[LJ-1.173]` measured that
Devlin's `Pow` is over the VARIABLE set and his arities are numeral. Say whether
his construction needs the general arity at all.** Return a **LITERATURE USED**
section.

## SCOPE (read)

`agents/tasks/LJ-1-173/lj-1.173-report.md` FIRST, then the cured fields
themselves.

## SCOPE (write)

`agents/tasks/LJ-1-199/` for probes. **A build lands in `src/` only after you
report.**

## MANDATORY RULES

Run `python3 scripts/rules.py --for build` and `--for probe`.

- **C-22.** Write your deliverable incrementally, never at the end.
- **C-36.** Write the term you could not write.
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
- **C-42.** A refutation measures the site it names, never its extent.
- **P-k, P-l, P-m, P-y, C-12, C-39, C-40. DD0, DD8, DD24, D-1, D-10, D-26,
  D-29, D-30. I-5.**

## CONSTRAINTS

- Count with `python3 scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with what closed and the actual lines against 255.** Then the seconds
with load and run count, and any wall with its elapsed figure. Then what is open
at `file:line`. Then the DD4 re-instantiation figure. Then what the satisfaction
layer still needs. **Mark every negative MEASURED or INFERRED.**
