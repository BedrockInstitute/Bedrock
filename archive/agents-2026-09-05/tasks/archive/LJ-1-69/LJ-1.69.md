# LJ-1.69: price one discharge, the number the campaign does not have

tier: codex (default)

## GOAL

**Measure one thing.** What does it cost to discharge ONE of `TwelveAgree`'s
twenty-four hypotheses? Nothing else.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, at `f111224`.
**The working tree carries an uncommitted, GREEN placement**:
`src/L/Condensation.lagda.md` at 6,390 in-fence lines against HEAD's 5,562.
**Do not discard it.**

## WHY THIS NUMBER AND NOT ANOTHER

The wing is 2.33 s over DD24, and **closing that does not save the wing**:
the pending wiring is measured at 0.045 to 0.047 s per line, 3.6x the bar,
so 500 more lines of it puts the wing about 19 s over on its own. I did that
arithmetic myself.

**The largest single piece of the pending wiring is the discharge.**
`TwelveAgree` (`src/L/Condensation.lagda.md:6406`) takes twenty-four
hypotheses:

```text
mem-out mem-back eq-out eq-back and-out and-back or-out or-back
imp-out imp-back neg-out neg-back top-out top-back bot-out bot-back
exist-out exist-back forall-out forall-back allin-out allin-back
exin-out exin-back
```

Discharging them means **applying the thirteen row modules** of the band.
**P-w says a module application COPIES its target's definitions**, and the
row modules are large. **Nobody has priced one.**

**So this dispatch measures one row application, and stops.** Everything
else in the campaign is currently being reasoned about without this number.

## THE INSTRUMENT, and it is `[LJ-1.66]`'s, which worked

`[LJ-1.66]` priced one `EnvSet` application at 1.016 s by adding N = 6
copies, measuring cold before and after, and dividing. **Use the same
instrument here.**

1. Pick ONE row module, and say why. `MemAgree` (`:4117`) is a reasonable
   default: its `out`/`back` are exactly `mem-out`/`mem-back`.
2. Add **N = 3** extra applications of it, at the frame the discharge would
   use, as unused bindings, changing nothing else. **N = 3 rather than 6,
   because if one application is as expensive as P-w predicts, six could
   cost minutes.**
3. Measure `L.Condensation` cold, three runs each side, same session, gate
   caliber, loads reported.
4. **Unit cost = delta / N.** Then remove the extra applications and confirm
   the tree is byte-identical to the start.

**If N = 3 walls on heap or runs past ten minutes per run, drop to N = 1 and
say so.** A heap exhaustion is a WALL with its seconds; never raise the cap.

## THEN THE ARITHMETIC, and it is the deliverable

Report:

- the unit cost of one row application;
- **times thirteen**, the discharge's projected cost;
- that figure against the wing's ceiling and against the 2.33 s residual.

**Say plainly whether the discharge alone exceeds the wing's whole budget.**

**A large number here is a full deliverable and probably the most useful
result of the phase.** It is not a failure; it is the price nobody has.

## WHAT YOU MUST NOT DO

- **Do not attempt a cure.** This dispatch measures. P-w's classes (a) and
  (b) are already measured false at this file (two hoists, one narrowing);
  class (c) is untried and is NOT your task.
- **Do not build the discharge.** Adding three unused applications is the
  instrument, not the wiring.
- **Do not delete the band.** `TwelveAgree`'s 24 hypotheses are discharged
  by exactly those thirteen row modules; `[LJ-1.64]` deleted them, the gate
  passed, and I reverted it. That is C-35.
- **Do not touch anything under `src/L/Coding/`.**
- **Count a module's exports by finding its boundary, not by guessing a line
  range.** I reported `EnvSet` at fifteen exports when it has eleven,
  because I read to `:2900` and swept in `TmVal`, which starts at `:2874`.
  `[LJ-1.68]` caught it. **If you report a count, say where the module
  ends.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

The row modules are the layer the J tower inherits, so their application
cost is a cost BOTH towers pay. **Say what your number implies for the J
tower**, and mark it MEASURED or INFERRED.

## ARCHIVE (DD18)

- **`_build/lj-1.66-report.md`**, read WHOLE. **Its section 1 is the
  instrument you are reusing.**
- **`_build/lj-1.68-report.md`**, read WHOLE. The narrowing negative, and
  the export-count correction.
- `_build/lj-1.66-review.md` section E.1, P-w's evidence.
- `_build/lj-1.62-report.md` sections 2-3, the wiring's 0.045 to 0.047 s per
  line and its P-n profile.
- `dev/LESSONS.md` **P-w**, P-m (`:2460`), P-n (`:2483`), P-l (`:2305`),
  read WHOLE.
- `archive/rud-route/` for SHAPE only.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature prices a spelling.** Say so in one line and
spend nothing.

## SCOPE (read)

`src/L/Condensation.lagda.md:6406-6480` (`TwelveAgree`'s telescope) FIRST,
then `:4117-4210` (`MemAgree`), then `_build/lj-1.66-report.md` section 1.

## SCOPE (write)

`src/L/Condensation.lagda.md` and `src/ProbeLJ169*.agda`. Your report is
`_build/lj-1.69-report.md`. **No other master. Never
`src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for probe`, and read every
statement.

- **D-1.** The probe doctrine. **This dispatch is a measurement, and it ends
  at the number.**
- **P-w.** A module application copies. **The prediction under test.**
- **P-m, P-n, P-l, P-q, P-t.**
- **P-h.** Module-parameterized, never function-parameterized.
- **P-k.** A read lemma is stated where its consumers use it.
- **R-35.** State the membership at the SMALL index and climb.
- **R-38.** Seal at the birth site, and do NOT unseal.
- **R-40.** State a membership witness SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process, cap never
  raised. **A heap exhaustion is a WALL with its seconds.**
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-35, C-36, C-37.**
- **D-8, D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **The tree carries uncommitted work
  that is not in HEAD.**
- Typecheck what you touch. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed.**
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose. Code and its own comments only.
- **The machine is quiet and both Agda slots are yours. Report the load
  average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.69-report.md` incrementally, skeleton first.

**Lead with the unit cost of one row-module application**, the N you used,
three runs each side, the spread and the load. Then the arithmetic: times
thirteen, against the wing's ceiling. Then whether the discharge alone
exceeds the wing's budget. **Mark every negative MEASURED or INFERRED.**
Then the DD4 answer and **the convergence answer.**
